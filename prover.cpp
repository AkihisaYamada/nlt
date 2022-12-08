#include<fstream>
#include"util.hpp"
#include"syntax.hpp"

using namespace std;

struct ProverFailure : exception {
	String message;
	ProverFailure(String const& message) : message(message) {}
};
class UnfinishedProof : std::exception {};

class Prover {
	unsigned int _depth;
	Ctxt _ctxt;
	bool _own_syntax;
	Ref<Syntax> _syntax;
	optional<CTerm> _thesis;
	StrMap<Rewriter> _rewriters;
	optional<Ref<Definer>> _definer;
	bool _exit_on_error;
	Prover(Prover const& parent, Ctxt const& ctxt, optional<CTerm> thesis) :
		_depth(parent._depth+1),
		_ctxt(ctxt),
		_syntax(parent._syntax),
		_own_syntax(false),
		_thesis(thesis),
		_rewriters(parent._rewriters),
		_definer(parent._definer) {}
public:
	Prover(istream& is, bool exit_on_error) :
		_depth(0),
		_ctxt(Ctxt::root()),
		_syntax(is),
		_own_syntax(true),
		_exit_on_error(exit_on_error) {
		_ctxt.fix(IMP_var);
		_ctxt.fix(ALL_var);
		_syntax->register_single_op('(');
		_syntax->register_single_op(')');
		_syntax->register_single_op('{');
		_syntax->register_single_op('}');
		_syntax->register_single_op('[');
		_syntax->register_single_op(']');
		_syntax->register_single_op(',');
		_syntax->register_single_op(';');
		_syntax->register_multi_op(':');
		_syntax->register_multi_op('*');
		_syntax->register_multi_op('+');
		_syntax->encloser("(",")",-1000,[]( std::optional<Term> t ){ return *t; });
		_syntax->infix(",",-1,-1,-2);
		_syntax->infix(";",-1,-1,-2);
		_syntax->infix(":",-1,-1,-2);
		_syntax->infix(":=",-1,-1,-2);
	}
	Prover branch() {
		return Prover(*this,_ctxt.branch(),optional<CTerm>());
	}
	Prover prove(CTerm const& thesis) {
		return Prover(*this,thesis.ctxt().branch(),thesis);
	}
	Thm get_thm() {
		Ctxt loc = _ctxt.branch();
		optional<Thm> thm = _gets_thm(loc);
		if( !thm.has_value() ) {
			throw Syntax::Error("expects a theorem");
		}
		return thm->intro();
	}

	Thm _rewrite( Ctxt const& loc, Thm const& source, bool rev = false ) {
		String name;
		if( _syntax->skips("[") ) {
			name = _syntax->get_token();
			_syntax->skip("]");
		}
		Rewriter& rewriter = _rewriters.find(name)->second;
		vector<char> pos;
		if( _syntax->skips("(") ) {
			while( !_syntax->skips(")") ) {
				pos.push_back(_syntax->get_int());
			}
		}
		bool many = _syntax->skips("*");
		Rewriter::Rules rules;
		for(;;) {
			auto const& opt_arg = _gets_thm(loc);
			if( !opt_arg.has_value() ) {
				break;
			}
			rules.add( rev ? rewriter.reverse(*opt_arg) : *opt_arg );
		}
		if( many ) {
			return rewriter.normalize(rules,source,255,pos);
		}
		auto const& opt_ret = rewriter.rewrite(rules,source,pos);
		if( !opt_ret.has_value() ) {
			throw ProverFailure("Failed unfold");
		}
		return *opt_ret;
	}

	optional<Thm> _gets_thm(Ctxt loc) {
		auto const& opt = _syntax->gets_thm_name();
		if( !opt.has_value() ) {
			return optional<Thm>();
		}
		Thm ret = loc.thm(*opt);
		for(;;) {
			if( _syntax->skips("(") ) {
				do {
					ret = ret.allE(loc.enclose(_syntax->get_term()));
				} while( _syntax->skips(",") );
				_syntax->skip(")");
			} else if( _syntax->skips("[") ) {
				if( _syntax->skips("OF") ) {
					for(;;) {
						auto const& opt_arg = _gets_thm(loc);
						if( !opt_arg.has_value() ) {
							break;
						}
						ret = discharge(ret,*opt_arg);
					}
				} else if( _syntax->skips("unfolded") ) {
					ret = _rewrite(loc,ret);
				} else if( _syntax->skips("folded") ) {
					ret = _rewrite(loc,ret,true);
				}
				_syntax->skip("]");
			} else {
				return ret;
			}
		}
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		for(;;) {
			optional<String> name = _syntax->gets_thm_name();
			if( !name.has_value() ) {
				break;
			}
			_syntax->skip(":");
			Thm thm = get_thm();
			ret.insert({*name,thm});
		}
		return ret;
	}
	optional<Term> gets_term() {
		optional<Term> const& term_opt = _syntax->gets_term();
		if( !term_opt.has_value() ) {
			return optional<Term>();
		}
		Term term = *term_opt;
		if( _syntax->skips("$") ) {
			CSubst subst = _ctxt.branch();
			do {
				String sym = _syntax->get_token();
				_syntax->skip(":=");
				subst.assign(sym,get_term());
			} while( _syntax->skips(",") );
			term = term.subst(subst);
		}
		return term;
	}
	Term get_term() {
		return *gets_term();
	}

	vector<pair<String,Term>> get_named_terms() {
		vector<pair<String,Term>> ret;
		for(;;) {
			optional<String> name = _syntax->gets_thm_name();
			if( !name.has_value() ) {
				break;
			}
			_syntax->skip(":");
			ret.push_back({*name,_syntax->get_term()});
			if( !_syntax->skips(",") ) {
				break;
			}
		}
		return ret;
	}

	optional<Thm> loop() {
		for(;;) try {
			for( int i = 0; i <= _depth; i++ ) {
				cout << '>';
			}
			cout << ' ' << flush;
			if( _syntax->skips("{") ) {
				cout << "Creating context." << endl;
				branch().loop();
				_syntax->skip("}");
				cout << "Left context." << endl;
			} else if( _syntax->skips("ctxt") ) {
				_syntax->skip(";");
				cout << _syntax->pretty_ctxt(_ctxt) << endl;
			} else if( _syntax->skips("fix") ) {
				cout << "Fixing";
				for(;;) {
					if( _syntax->skips(";") ) break;
					String sym = _syntax->get_token();
					_ctxt.fix(sym);
					cout << ' ' << sym << flush;
				}
				cout << ';' << endl;
			} else if( _syntax->skips("assume") ) {
				cout << "Assuming ";
				for(;;) {
					String name = _syntax->get_thm_name();
					_syntax->skip(":");
					Term term = _syntax->gets_term(0).value();
					cout << name << ": " << _syntax->pretty_term(term) << flush;
					_ctxt.assume(name,term);
					if( !_syntax->skips(",") ) {
						break;
					}
					cout << ", " << flush;
				}
				_syntax->skip(";");
				cout << endl;
			} else if( _syntax->skips("thm") ) {
				Thm thm = get_thm();
				_syntax->skip(";");
				cout << "thm " << _syntax->pretty_thm(thm) << endl;
			} else if( _syntax->skips("term") ) {
				Term term = get_term();
				_syntax->skip(";");
				cout << "term " << _syntax->pretty_term(term) << endl;
			} else if( _syntax->skips("name") ) {
				String name = _syntax->get_thm_name();
				_syntax->skip(":");
				_ctxt.claim(name,get_thm());
				_syntax->skip(";");
				cout << "lemma " << name << ": " << _syntax->pretty_thm(_ctxt.thm(name)) << endl;
			} else if( _syntax->skips("move") ) {
				Ctxt pctxt = *_ctxt.find_ctxt();
				String name = _syntax->get_thm_name();
				_syntax->skip(":");
				pctxt.claim(name,get_thm().intro());
				_syntax->skip(";");
				cout << "theorem " << name << ": " << _syntax->pretty_thm(pctxt.thm(name)) << endl;
			} else if( _syntax->skips("show") ) {
				String thm_name = _syntax->get_thm_name();
				_syntax->skip(":");
				Ctxt stmt_ctxt = _ctxt.branch();
				CTerm stmt = stmt_ctxt.enclose(_syntax->get_term(0));
				_syntax->skip(";");
				cout << "Proving " << thm_name << ": " << _syntax->pretty_term(stmt) << endl;
				auto const& thm_opt = prove(stmt).loop();
				if( !thm_opt.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Thm thm = *thm_opt;
				CTerm stmt_strip = strip_all(stmt,stmt_ctxt);
				Ctxt thm_ctxt = stmt_ctxt.branch();
				Thm thm_strip = strip_all(thm,thm_ctxt);
				stmt_strip = stmt_strip.weaken(thm_ctxt);
				optional<CSubst> matcher = match(thm_ctxt.fvars(),thm_strip,stmt_strip);
				if( !matcher.has_value() ) {
					cout << "ERROR: Proof mismatch " << _syntax->pretty_term(thm) << endl;
					throw UnfinishedProof();
				}
				thm = thm.weaken(stmt_ctxt);
				for( auto const& v : thm_ctxt.fvar_list() ) {
					thm = thm.allE(matcher->get(v)->subst(stmt_ctxt));
				}
				thm = thm.intro();
				_ctxt.claim(thm_name,thm);
			} else if( _syntax->skips("obtain") ) {
				String sym = _syntax->get_token();
				_syntax->skip("where");
				auto specs = get_named_terms();
				_syntax->skip(";");
				auto const& pair = _ctxt.obtain(sym,specs);
				CTerm const& goal = pair.first;
				Ctxt const& obtainer = pair.second;
				cout << "Obtaining " << sym << " where ";
				for( auto& spec : specs ) {
					cout << spec.first << ": " << _syntax->pretty_term(spec.second) << ", ";
				}
				cout << endl << "Proving " << _syntax->pretty_term(goal) << endl;
				auto const& thm_opt = prove(goal).loop();
				if( !thm_opt.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Thm const& thm = *thm_opt;
				if( goal != thm ) {
					cout << "ERROR: Proof mismatch " << _syntax->pretty_term(thm) << endl;
					throw UnfinishedProof();
				}
				_ctxt.import(obtainer.interpret(CSubst(_ctxt),{thm}));
				cout << "Obtained " << sym << endl;
			} else if( _syntax->skips("define") ) {
				optional<String> name;
				if( _syntax->skips("(") ) {
					name = _syntax->get_token();
					_syntax->skip(")");
				}
				Term l = get_term();
				_syntax->skip(":=");
				Term r = get_term();
				_syntax->skip(";");
				(**_definer).define(_ctxt,l,r,name);
				cout << "Defined " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _syntax->skips("by") ) {
				if( !_thesis.has_value() ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm ret = get_thm();
				_syntax->skip(";");
				cerr << "By " << _syntax->pretty_thm(ret) << endl;
				return ret.intro();
			} else if( _syntax->skips("prefix") ) {
				String sym = _syntax->get_token();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( _syntax->skips("infix") ) {
				String sym = _syntax->get_token();
				int llevel = _syntax->get_int();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else if( _syntax->skips("setup") ) {
				if( _syntax->skips("rewrite") ) {
					String name;
					if( _syntax->skips("[") ) {
						name = _syntax->get_token();
						_syntax->skip("]");
					}
					Thm const& imp = get_thm();
					Thm const& sym = get_thm();
					Thm const& refl = get_thm();
					Thm const& trans = get_thm();
					auto const& pair = _rewriters.insert({name,Rewriter(imp,sym,refl,trans)});
					cout << "Initialized Rewriter " << name << endl;
				} else if( _syntax->skips("cong") ) {
					String name;
					if( _syntax->skips("[") ) {
						name = _syntax->get_token();
						_syntax->skip("]");
					}
					Rewriter& rewriter = _rewriters.find(name)->second;
					for(;;) {
						if( _syntax->skips("!") ) {
							CTerm cong_pat = _ctxt.branch().enclose(get_term());
							_syntax->skip(":");
							Thm const& cong_rule = get_thm();
							rewriter.register_quantifier_cong(cong_pat,cong_rule);
						} else {
							CTerm cong_pat = _ctxt.branch().enclose(get_term());
							_syntax->skip(":");
							Thm const& cong_rule = get_thm();
							rewriter.register_cong(cong_pat,cong_rule);
						}
						if( !_syntax->skips(",") ) {
							break;
						}
					}
				} else if( _syntax->skips("define") ) {
					String const& eq = _syntax->get_token();
					String const& lam = _syntax->get_token();
					Thm const& beta = get_thm();
					cerr << "equality: " << eq << " lambda: " << lam << " beta: " << _syntax->pretty_thm(beta) << endl;
					Rewriter const& rewriter = _rewriters.find(String())->second;
					_definer = optional(Definer(rewriter,eq,lam,beta));
				} else if( _syntax->skips("set_comprehension") ) {
					Term const& empty = _syntax->get_term(1000);
					Term const& singleton = _syntax->get_term(1000);
					Term const& collect = _syntax->get_term(1000);
					Term const& lam = _syntax->get_term(1000);
					auto handler = [=](optional<Term> inner) {
						if( !inner.has_value() ) {
							return empty;
						}
						if( inner->abs().has_value() ) {
							return collect(lam(*inner));
						}
						return singleton(*inner);
					};
					_syntax->encloser("{","}",-1000,handler);
				}
				_syntax->skip(";");
			} else if( _syntax->skips("symbol") ) {
				bool solo = _syntax->skips("solo");
				while( !_syntax->skips(";") ) {
					string const& sym = _syntax->get_token();
					int ch = int_of_chars(sym.data());
					if( solo ) {
						_syntax->register_single_op(ch);
					} else {
						_syntax->register_multi_op(ch);
					}
				}
			} else if( _syntax->skips("sorry") ) {
				_syntax->skip(";");
				Thm ret = sorry(*_thesis);
				ret = ret.intro();
				cerr << "!!! SORRY !!! " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else {
				return optional<Thm>();
			}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << _syntax->pretty_term(e.imp) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			exit(-1);
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << _syntax->pretty_term(e.all) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			exit(-1);
		} catch ( TheoremNotFound const& e ) {
			cerr << "ERROR: No thm \"" << e.name << "\" found" << endl;
			exit(-1);
		} catch ( UnexpectedTerm const& e ) {
			cerr << "ERROR: Unexpected term " << _syntax->pretty_term(e.term) << endl;
			exit(-1);
		} catch ( UnboundVariable const& e ) {
			cerr << "ERROR: Unbound variable " << e.name << endl;
			exit(-1);
		} catch ( Syntax::Error const& e ) {
			cerr << "Syntax ERROR: " << e.message << endl;
			exit(-1);
		}
	}
private:
	void _make_own_syntax() {
		if( !_own_syntax ) {
			_syntax = Ref(*_syntax);
			_own_syntax = true;
		}
	}
};

int main(int argc, char* argv[]) {
	istream* pis;
	bool exit_on_error = false;
	if( argc == 1 ) {
		pis = &cin;
	} else {
		pis = new fstream(argv[1]);
		exit_on_error = true;
	}
	Prover prover = Prover(*pis,exit_on_error);
	prover.loop();
	cout << "bye!" << endl;
	return 0;
}

