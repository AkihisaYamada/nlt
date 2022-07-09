#include "theories.hpp"
#include "lexer.hpp"

using namespace std;

inline ostream& operator<<(
        ostream& stream, 
        const function<ostream& (ostream&)>& manipulator) {
    return manipulator( stream );
}

class UnfinishedProof : std::exception {};

Term const SEMICOLON = Term(";");
Term const COMMA = Term(",");

class Prover {
	struct Prefix {
		int llevel;
		int rlevel;
	};
	struct Infix {
		int level;
		int llevel;
		int rlevel;
	};
	typedef map<string,Prefix,less<>> PrefixTable;
	typedef map<string,Infix,less<>> InfixTable;
	struct Thesis {
		string_view name;
		Ctxt ctxt;
		Term claim;
	};
	Ref<Lexer> lexer;
	Ctxt ctxt;
	Ref<PrefixTable> prefixes;
	Ref<InfixTable> infixes;
	optional<Thesis> thesis;
public:
	Prover() : lexer(Lexer(cin)), ctxt("root"), infixes({
		{",",{-1,-1,-2}},
		{";",{-1,-1,-2}},
	}), prefixes(PrefixTable()) {}
	Prover(Prover const& parent, string_view name = "") :
		lexer(parent.lexer),
		ctxt(parent.ctxt.branch()),
		infixes(parent.infixes),
		prefixes(parent.prefixes),
		thesis(optional<Thesis>()) {}
	Prover(Prover const& parent, string_view thm_name, Term const& claim) :
		lexer(parent.lexer),
		ctxt(parent.ctxt.branch()),
		infixes(parent.infixes),
		prefixes(parent.prefixes),
		thesis({thm_name,parent.ctxt,claim}) {}
	function<ostream&(ostream&)> pretty_term(Term const& term, int level = -1000) const {
		return [&](ostream& os) -> ostream& {
			auto sym = term.sym();
			if( sym != NULL ) {
				if( prefixes->contains(*sym) || infixes->contains(*sym) ) {
					return os << '(' << *sym << ')';
				}
				return os << *sym;
			}
			auto app1 = term.app();
			if( app1 != NULL ) {
				auto sym = app1->fun.sym();
				if( sym != NULL ) {
					auto it = prefixes->find(*sym);
					if( it != prefixes->end() ) {
						auto& op = it->second;
						if( level >= op.llevel ) {
							os << '(';
						}
						os << *sym << ' ' << pretty_term(app1->arg,op.rlevel);
						if( level >= op.llevel ) {
							os << ')';
						}
						return os;
					}
				} else {
					auto app2 = app1->fun.app();
					if( app2 != NULL ) {
						auto sym = app2->fun.sym();
						if( sym != NULL ) {
							auto it = infixes->find(*sym);
							if( it != infixes->end() ) {
								auto& op = it->second;
								if( level >= op.level ) {
									os << '(';
								}
								os << pretty_term(app2->arg,op.llevel);
								os << ' ' << *sym << ' ';
								os << pretty_term(app1->arg,op.rlevel);
								if( level >= op.level ) {
									os << ')';
								}
								return os;
							}
						}
					}
				}
				if( level >= 1000 ) {
					os << '(';
				}
				os << pretty_term(app1->fun, 999) << ' ';
				os << pretty_term(app1->arg, 1000);
				if( level >= 1000 ) {
					os << ')';
				}
				return os;
			}
			auto abs = term.abs();
			if( abs != NULL ) {
				return os << abs->var << ". " << pretty_term(abs->body, 0);
			}
			auto fix = term.fix();
			if( fix != NULL ) {
				return os << fix->var << ".[" << pretty_term(fix->val) << ']';
			}
			assert(false);
		};
	}
	function<ostream&(ostream&)> pretty_thm(Thm const& thm) const {
		return [&](ostream& os) -> ostream& {
			string_view name = thm.ctxt().name();
			if( name != "" ) {
				os << "(in " << name << ") ";
			}
			return os << pretty_term(thm);
		};
	}

	function<ostream&(ostream&)> pretty_ctxt(Ctxt const& ctxt) const {
		return [&](ostream& os) -> ostream& {
			os << "ctxt " << ctxt.name() << " {" << endl;
			for( auto sym : ctxt.sym_list() ) {
				os << "  sym " << sym << endl;
			}
			for( auto assm : ctxt.assms() ) {
				os << "  assm " << pretty_term(assm) << endl;
			}
			for( auto thm : ctxt.thms() ) {
				os << "  thm " << thm.first << ": " << pretty_term(thm.second) << endl;
			}
			os << "}" << endl;
			return os;
		};
	}

	string get_thm_name() {
		if( lexer->next_token_type() != Lexer::Word ) {
			return lexer->get_token();
		}
		string ret = lexer->get_token();
		for(;;) {
			if( !lexer->skips('.') ) {
				return ret;
			}
			ret += '.';
			if( lexer->next_token_type() != Lexer::Word ) {
				return ret;
			}
			ret += lexer->get_token();
		}
	}
	optional<Term> get_term(int level = 0) {
		if( !lexer->readable() ) {
			return optional<Term>();
		}
		Term ret = Term("");
		if( lexer->skips('(') ) {
			ret = get_term(0).value();
			lexer->skip(')');
		} else {
			string_view sym = lexer->peek_token();
			auto it = prefixes->find(sym);
			if( it != prefixes->end() ) {
				if( it->second.llevel < level ) {
					return optional<Term>();
				}
				ret = Term(it->first);
				lexer->ignore_token();
				auto r = get_term(it->second.rlevel);
				if( r.has_value() ) {
					ret = ret(r.value());
				}
			} else {
				string sym = lexer->get_token();
				if( lexer->skips('.') ) {
					ret = sym /= get_term(level).value();
				} else if( lexer->skips('[') ) {
					ret = sym / get_term(0).value();
					lexer->skip(']');
				} else {
					ret = Term(sym);
				}
			}
		}
		for(;;) {
			string_view sym = lexer->peek_token();
			if( sym == "" || sym == ")" || sym == "]" || sym == "}" ) {
				return ret;
			}
			auto pair = infixes->find(sym);
			int rlevel;
			if( pair == infixes->end() ) {
				if( 1000 <= level ) {
					return ret;
				}
				rlevel = 1000;
			} else {
				if( pair->second.llevel < level ) {
					return ret;
				}
				ret = Term(pair->first)(ret);
				lexer->ignore_token();
				rlevel = pair->second.rlevel;
			}
			auto r = get_term(rlevel);
			if( r.has_value() ) {
				ret = ret(r.value());
			} else {
				return ret;
			}
		}
	}

	Thm get_thm(Ctxt const& ctxt) {
		Thm ret = ctxt.thm(get_thm_name());
		for(;;) {
			if( lexer->skips('(') ) {
				do {
					ret = ret.of(get_term().value());
				} while( lexer->skips(',') );
				lexer->skip(')');
			} else if( lexer->skips('[') ) {
				do {
					ret = ret.OF(get_thm(ctxt));
				} while	( lexer->skips(',') );
				lexer->skip(']');
			} else {
				return ret;
			}
		}
	}
	void loop() {
		try {
		cout << "Entering ";
		if( ctxt.name() == "" ) {
			cout << "unnamed context." << endl;
		} else {
			cout << "context " << ctxt.name() << endl;
		}
		for(;;) {
			cout << "> " << flush;
			if( lexer->skips('{') ) {
				Prover(*this).loop();
			} else if( lexer->skips("ctxt") ) {
				lexer->skip(';');
				cout << pretty_ctxt(ctxt) << endl;
			} else if( lexer->skips("fix") ) {
				for(;;) {
					if( lexer->skips(';') ) break;
					string sym = lexer->get_token();
					ctxt.fix(sym);
					cout << "Fixed " << sym << endl;
				}
			} else if( lexer->skips("assume") ) {
				string name = get_thm_name();
				lexer->skip(':');
				Term term = get_term(0).value();
				lexer->skip(';');
				ctxt.assume(name,term);
				cout << "Assumed " << name << ": " << pretty_term(term) << endl;
			} else if( lexer->skips("thm") ) {
				Thm thm = get_thm(ctxt);
				lexer->skip(';');
				cout << "thm " << pretty_thm(thm) << endl;
			} else if( lexer->skips("term") ) {
				Term term = get_term(0).value();
				lexer->skip(';');
				cout << "term " << pretty_term(term) << endl;
			} else if( lexer->skips("name") ) {
				string name = get_thm_name();
				lexer->skip(':');
				ctxt.claim(name,get_thm(ctxt));
				lexer->skip(';');
				cout << "lemma " << name << ": " << pretty_thm(ctxt.thm(name)) << endl;
			} else if( lexer->skips("move") ) {
				Ctxt pctxt = ctxt.parent().value();
				string name = get_thm_name();
				lexer->skip(':');
				pctxt.claim(name,get_thm(ctxt));
				lexer->skip(';');
				cout << "theorem " << name << ": " << pretty_thm(pctxt.thm(name)) << endl;
			} else if( lexer->skips("show") ) {
				string thm_name = get_thm_name();
				lexer->skip(':');
				Term thesis = get_term(0).value();
				lexer->skip(';');
				Prover(*this,thm_name,thesis).loop();
				cout << "theorem " << thm_name << pretty_thm(ctxt.thm(thm_name)) << endl;
			} else if( lexer->skips("by") ) {
				if( !thesis.has_value() ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				auto thm = thesis.value();
				Ctxt target_ctxt = thm.ctxt;
				target_ctxt.claim(thm.name,get_thm(ctxt));
				lexer->skip(';');
				cout << "Leaving the proof context" << endl;
				return;
			} else if( lexer->skips('}') ) {
				cout << "Leaving context " << ctxt.name() << endl;
				return;
			} else if( lexer->skips("prefix") ) {
				Term sym = Term(lexer->get_token());
				int level = lexer->get_int();
				int rlevel = lexer->get_int();
				prefixes->insert({*sym.sym(),{level,rlevel}});
				lexer->skips(';');
				cout << "New prefix operator " << sym << endl;
			} else if( lexer->skips("infix") ) {
				Term sym = Term(lexer->get_token());
				int level = lexer->get_int();
				int llevel = lexer->get_int();
				int rlevel = lexer->get_int();
				infixes->insert({*sym.sym(),{level,llevel,rlevel}});
				lexer->skips(';');
				cout << "New infix operator " << sym << endl;
			} else {
				cerr << "Unexpected " << lexer->peek_token() << endl;
				throw SyntaxError();
			}
		}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << pretty_term(e.imp) << endl << "\nwith\t" << pretty_term(e.arg) << endl;
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << pretty_term(e.all) << endl << "\nwith\t" << pretty_term(e.arg) << endl;
		}
	}
};

int main() {
	Prover obj;
	obj.loop();
	return 0;
}

