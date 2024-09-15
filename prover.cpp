#include<fstream>
#include"definer.hpp"
#include"concluder.hpp"

using namespace std;

struct ProverFailure : exception {
	string message;
	ProverFailure(string const& message) : message(message) {}
};
class UnfinishedProof : exception {};

class Prover {
	unsigned int _depth;
	Ctxt _ctxt;
	bool _own_syntax;
	Ref<Parser> _syntax;
	Opt<Thm> _thesis;
	Concluder _concluder;
	StrMap<Ref<Rewriter>> _rewriters;
	OptRef<Definer> _definer;
	bool _exit_on_error;
	Prover(Prover const& parent, Ctxt const& ctxt, Opt<Thm> thesis) :
		_depth(parent._depth+1),
		_ctxt(ctxt),
		_syntax(parent._syntax),
		_own_syntax(false),
		_thesis(thesis),
		_concluder(parent._concluder),
		_rewriters(parent._rewriters),
		_definer(parent._definer) {}
	void _error() {
		if( _exit_on_error ) {
			exit(-1);
		}
	}
public:
	Prover(istream& is, bool exit_on_error) :
		_depth(0),
		_ctxt(Ctxt()),
		_syntax(Ref<Parser>::make<istream&>(is)),
		_own_syntax(true),
		_exit_on_error(exit_on_error) {
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
		_syntax->encloser("(",")",-1000,[&]( Parser& parser ){
			Opt<Term> t = parser.gets_term(0);
			_syntax->skip(")");
			return *t;
		});
		_syntax->infix(",",-1,-1,-2);
		_syntax->infix(";",-1,-1,-2);
		_syntax->infix(":",-1,-1,-2);
		_syntax->infix(":=",-1,-1,-2);
	}
	Prover branch() {
		return Prover(*this,_ctxt.branch(),Opt<Thm>());
	}
	Prover prove(CTerm const& thesis) {
		Ctxt const& ctxt = thesis.ctxt();
		Ctxt loc = ctxt.branch();
		Thm thm = loc.assume(thesis).intro();// thesis ⟹ thesis
		Ctxt ctxt2 = ctxt.branch();
		return Prover(*this,ctxt2,thm);
	}
	Thm get_thm() {
		Ctxt loc = _ctxt.branch();
		if( auto const& thm = _gets_thm(loc) ) {
			return thm->intro();
		} else {
			throw Parser::Error("expects a theorem");
		}
	}
	Ref<Rewriter>& _rewriter() {
		string name;
		if( _syntax->skips("[") ) {
			name = _syntax->get_token();
			_syntax->skip("]");
		}
		return _rewriters.find(name)->second;
	}
	Thm _rewrite( Rewriter const& rewriter, Ctxt const& loc, Thm const& source, vector<char> pos, bool rev = false ) {
		if( _syntax->skips("(") ) {
			while( !_syntax->skips(")") ) {
				pos.push_back(_syntax->get_int());
			}
		}
		unsigned int min, max;
		if( _syntax->skips("*") ) {
			min = 0; max = 255;
		} else if( _syntax->skips("+") ) {
			min = 1; max = 255;
		} else {
			min = 1; max = 1;
		}
		Rewriter::Rules rules;
		while( auto const& arg = _gets_thm(loc) ) {
			rules.add( rev ? rewriter.reverse(*arg) : *arg );
		}
		return rewriter.rewrite(rules,source,min,max,pos);
	}

	Opt<Thm> _gets_thm(Ctxt loc) {
		auto const& opt = _syntax->gets_thm_name();
		if( !opt ) {
			return {};
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
					while( auto const& arg = _gets_thm(loc) ) {
						ret = discharge(ret,*arg);
					}
				} else if( _syntax->skips("unfolded") ) {
					auto const& rewriter = *_rewriter();
					ret = _rewrite(rewriter,loc,ret,{},false);
				} else if( _syntax->skips("folded") ) {
					auto const& rewriter = *_rewriter();
					ret = _rewrite(rewriter,loc,ret,{},true);
				}
				_syntax->skip("]");
			} else {
				return ret;
			}
		}
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		while( auto const& name = _syntax->gets_thm_name() ) {
			_syntax->skip(":");
			Thm const& thm = get_thm();
			ret.insert({*name,thm});
		}
		return ret;
	}
	Opt<Term> gets_term() {
		if( auto const& term = _syntax->gets_term() ) {
			Term ret = *term;
			if( _syntax->skips("$") ) {
				CSubst subst = _ctxt.branch();
				do {
					string sym = _syntax->get_token();
					_syntax->skip(":=");
					subst.assign(sym,get_term());
				} while( _syntax->skips(",") );
				ret = ret.subst(subst);
			}
			return ret;
		}
		return {};
	}
	Term get_term() {
		if( auto const& term = gets_term() ) {
			return *term;
		}
		throw Syntax::Error("Expects a term");
	}

	vector<pair<string,Term>> get_named_terms() {
		vector<pair<string,Term>> ret;
		for(;;) {
			auto const& name = _syntax->gets_thm_name();
			if(!name) {
				return ret;
			}
			_syntax->skip(":");
			ret.push_back({*name,_syntax->get_term(0)});
			if( !_syntax->skips(",") ) {
				return ret;
			}
		}
	}

	void _flush() {
		cout << flush;
	}
	void _indent() {
		for( int i = 0; i <= _depth; i++ ) {
			cout << '>';
		}
		cout << ' ';
	}
	Opt<Thm> loop() {
		for(;;) try {
			_indent();
			_flush();
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
					string sym = _syntax->get_token();
					_ctxt.fix(sym);
					cout << ' ' << sym << flush;
				}
				cout << ';' << endl;
			} else if( _syntax->skips("assume") ) {
				cout << "Assuming ";
				for(;;) {
					string name = _syntax->get_thm_name();
					_syntax->skip(":");
					Term term = _syntax->get_term(0);
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
				string name = _syntax->get_thm_name();
				_syntax->skip(":");
				_ctxt.claim(name,get_thm());
				_syntax->skip(";");
				cout << "lemma " << name << ": " << _syntax->pretty_thm(_ctxt.thm(name)) << endl;
			} else if( _syntax->skips("move") ) {
				Ctxt pctxt = *_ctxt.find_ctxt();
				string name = _syntax->get_thm_name();
				_syntax->skip(":");
				pctxt.claim(name,get_thm().intro());
				_syntax->skip(";");
				cout << "theorem " << name << ": " << _syntax->pretty_thm(pctxt.thm(name)) << endl;
			} else if( _syntax->skips("show") ) {
				string thm_name = _syntax->get_thm_name();
				_syntax->skip(":");
				Ctxt stmt_ctxt = _ctxt.branch();
				CTerm stmt = stmt_ctxt.enclose(_syntax->get_term(0));
				cout << "Show " << thm_name << ": " << _syntax->pretty_term(stmt);
				if( _syntax->skips(",") ) {
					_syntax->skip("assuming");
					cout << ", assuming " << flush;
					for(;;) {
						string assm_name = _syntax->get_thm_name();
						_syntax->skip(":");
						Term term = _syntax->get_term(0);
						cout << assm_name << ": " << _syntax->pretty_term(term) << flush;
						stmt_ctxt.assume(assm_name,term);
						if( !_syntax->skips(",") ) {
							break;
						}
						cout << ", " << flush;
					}
				}
				cout << endl;
				_syntax->skip(";");
				auto const& thm = prove(stmt).loop();
				if( !thm ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				_ctxt.claim(thm_name,thm->intro());
			} else if( _syntax->skips("obtain") ) {
				string sym = _syntax->get_token();
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
				if( !thm_opt ) {
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
				Opt<string> name;
				if( _syntax->skips("(") ) {
					name = _syntax->get_token();
					_syntax->skip(")");
				}
				Term l = get_term();
				_syntax->skip(":=");
				Term r = get_term();
				_syntax->skip(";");
				if( !_definer ) {
					throw ProverFailure("definer not setup");
				}
				_definer->define(_ctxt,l,r,name);
				cout << "Defined " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _syntax->skips("unfold") ) {
				if( !_thesis ) {
					cerr << "No goal for \"unfold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				Ctxt const& loc = _thesis->ctxt();
				*_thesis = _rewrite(rewriter,loc,*_thesis,{0});
				_syntax->skip(";");
				cout << "unfold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else if( _syntax->skips("fold") ) {
				if( !_thesis ) {
					cerr << "No goal for \"fold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				Ctxt const& loc = _thesis->ctxt();
				*_thesis = _rewrite(rewriter,loc,*_thesis,{0},true);
				_syntax->skip(";");
				cout << "fold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else if( _syntax->skips("by") ) {
				if( !_thesis ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm const& thm = get_thm().intro();
				_syntax->skip(";");
				CTerm stmt = _thesis->app()->first.app()->second;
				Ctxt stmt_ctxt = stmt.ctxt().branch();
				CTerm stmt_strip = strip_all(stmt,stmt_ctxt);
				Ctxt thm_ctxt = stmt_ctxt.branch();
				Thm thm_strip = strip_all(thm,thm_ctxt);
				stmt_strip = stmt_strip.weaken(thm_ctxt);
				Opt<CSubst> matcher = match(thm_ctxt.fvars(),thm_strip,stmt_strip);
				if( !matcher ) {
					cout << "ERROR: Proof mismatch " << _syntax->pretty_term(thm) << endl;
					throw UnfinishedProof();
				}
				Thm arg = thm.weaken(stmt_ctxt);
				for( auto const& v : thm_ctxt.fvar_list() ) {
					arg = arg.allE(matcher->get(v)->subst(stmt_ctxt));
				}
				arg = arg.intro();
				Thm const& ret = _thesis->impE(arg);
				cout << "Concluded " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else if( _syntax->skips("done") ) {
				if( !_thesis ) {
					cerr << "No goal for \"done\"" << endl;
					throw UnfinishedProof();
				}
				_syntax->skip(";");
				cout << "Done." << endl;
				return _concluder.conclude(*_thesis);
			} else if( _syntax->skips("prefix") ) {
				string sym = _syntax->get_token();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( _syntax->skips("infix") ) {
				string sym = _syntax->get_token();
				int llevel = _syntax->get_int();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else if( _syntax->skips("setup") ) {
				if( _syntax->skips("conclude") ) {
					Thm const& thm = get_thm();
					_concluder.insert(thm);
					cout << "Added concluder: " << _syntax->pretty_thm(thm) << endl;
				} else if( _syntax->skips("rewrite") ) {
					string name;
					if( _syntax->skips("[") ) {
						name = _syntax->get_token();
						_syntax->skip("]");
					}
					Thm const& refl = get_thm();
					Thm const& sym = get_thm();
					Thm const& trans = get_thm();
					Thm const& imp = get_thm();
					auto const& pair = _rewriters.insert({name,Ref<Rewriter>::make(refl,sym,trans,imp)});
					cout << "Initialized Rewriter " << name <<
						"\n\trefl: " << _syntax->pretty_term(refl) <<
						"\n\tsym: " << _syntax->pretty_term(sym) <<
						"\n\ttrans: " << _syntax->pretty_term(trans) <<
						"\n\timp: " << _syntax->pretty_term(imp) << endl;
				} else if( _syntax->skips("cong") ) {
					Rewriter& rewriter = *_rewriter();
					cout << "Registering Congruence:" << endl;
					for(;;) {
						if( _syntax->skips("!") ) {
							CTerm cong_pat = _ctxt.branch().enclose(get_term());
							_syntax->skip(":");
							Thm const& cong_thm = get_thm();
							rewriter.register_quantifier_cong(cong_pat,cong_thm);
							cout << "\tquantifier [" << _syntax->pretty_term(cong_pat) <<
								 "] " << _syntax->pretty_thm(cong_thm) << endl;
						} else {
							CTerm cong_pat = _ctxt.branch().enclose(get_term());
							_syntax->skip(":");
							Thm const& cong_thm = get_thm();
							rewriter.register_cong(cong_pat,cong_thm);
							cout << "\t[" << _syntax->pretty_term(cong_pat) <<
								 "] " << _syntax->pretty_thm(cong_thm) << endl;
						}
						if( !_syntax->skips(",") ) {
							break;
						}
					}
				} else if( _syntax->skips("define") ) {
					string const& eq = _syntax->get_token();
					string const& lam = _syntax->get_token();
					Thm const& beta = get_thm();
					cerr << "equality: " << eq << " lambda: " << lam << " beta: " << _syntax->pretty_thm(beta) << endl;
					auto const& rewriter = _rewriters.find(string())->second;
					_definer = OptRef<Definer>::make(rewriter,eq,lam,beta);
				} else if( _syntax->skips("set_comprehension") ) {
					Term const& empty = _syntax->get_term(1000);
					Term const& singleton = _syntax->get_term(1000);
					Term const& collect = _syntax->get_term(1000);
					Term const& lam = _syntax->get_term(1000);
					Term const& un = _syntax->get_term(1000);
					auto handler = [=,*this](Parser& parser) {
						auto const& inner = parser.gets_term(0);
						if( !inner ) {
							_syntax->skip("}");
							return empty;
						}
						if( inner->abs() ) {
							_syntax->skip("}");
							return collect(lam(*inner));
						}
						Term ret = singleton(*inner);
						while( _syntax->skips(",") ) {
							auto const inner2 = parser.gets_term(0);
							ret = un(ret)(singleton(*inner2));
						}
						_syntax->skip("}");
						return ret;
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
				Thm ret = sorry(_thesis->app()->second);
				cerr << "!!! SORRY !!! " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else {
				return Opt<Thm>();
			}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << _syntax->pretty_term(e.imp) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			_error();
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << _syntax->pretty_term(e.all) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			_error();
		} catch ( TheoremNotFound const& e ) {
			cerr << "ERROR: No thm \"" << e.name << "\" found" << endl;
			_error();
		} catch ( Error const& e ) {
			cerr << "ERROR: Unexpected term " << _syntax->pretty_term(e.term) << endl;
			_error();
		} catch ( UnboundVariable const& e ) {
			cerr << "ERROR: Unbound variable " << e.name << endl;
			_error();
		} catch ( Syntax::Error const& e ) {
			cerr << "Syntax ERROR: " << e.message << endl;
			_error();
		} catch ( Rewriter::TooFewSteps const& e ) {
			cerr << "Rewriter ERROR: Too few steps on: " << _syntax->pretty_term(e.term) << endl;
			_error();
		} catch ( Rewriter::TooManySteps const& e ) {
			cerr << "Rewriter ERROR: Too many steps on: " << _syntax->pretty_term(e.term) << endl;
			_error();
		} catch ( exception const& e ) {
			cerr << "Other exception: " << e.what() << endl;
			_error();
		}
	}
private:
	void _make_own_syntax() {
		if( !_own_syntax ) {
			_syntax.fork();
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

