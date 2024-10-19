#include<fstream>
#include<ranges>
#include"locale.hpp"
#include"parser.hpp"
#include"definer.hpp"
#include"concluder.hpp"

using namespace std;

struct ProverFailure : exception {
	string message;
	ProverFailure(string const& message) : message(message) {}
};
class UnfinishedProof : exception {};

Lex LEX = [&]{
	Lex ret;
	ret.register_multi_op(int_of_chars("∀"));
	ret.register_multi_op(int_of_chars("⟹"));
	ret.register_single_op(',');
	ret.register_single_op(';');
	ret.register_multi_op(':');
	ret.register_multi_op('*');
	ret.register_multi_op('+');
	return ret;
}();

class Prover {
	unsigned int _depth;
	Locale _loc;
	bool _own_syntax;
	Ref<Parser> _syntax;
	Opt<Thm> _thesis;
	Concluder _concluder;
	StrMap<Ref<Rewriter>> _rewriters;
	OptRef<Definer> _definer;
	bool _exit_on_error;
	Prover(Prover const& parent, Locale const& loc, Opt<Thm> thesis) :
		_depth(parent._depth+1),
		_loc(loc),
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
		_loc(),
		_syntax(Ref<Parser>::make<istream&>(is)),
		_own_syntax(true),
		_exit_on_error(exit_on_error) {
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
		return Prover(*this,_loc.branch(),Opt<Thm>());
	}
	Prover prove(Locale const& loc, CTerm const& thesis) {
		Ctxt ctxt = loc.branch();
		Thm thm = ctxt.assume(thesis).intro();// thesis ⟹ thesis
		return Prover(*this,loc.branch(),thm);
	}
	Thm get_thm() {
		auto loc = _loc.branch();
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
	Thm _rewrite( Rewriter const& rewriter, Locale& loc, Thm const& source, vector<char> pos, bool rev = false ) {
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

	Opt<Thm> _gets_thm(Locale& loc) {
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
				CSubst subst = _loc.branch();
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
		throw Error("Expects a term");
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
				cout << _loc.pretty(*_syntax) << endl;
			} else if( _syntax->skips("fix") ) {
				cout << "Fixing";
				for(;;) {
					if( _syntax->skips(";") ) break;
					string sym = _syntax->get_token();
					_loc.fix(sym);
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
					_loc.assume(name,term);
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
				_loc.add_thm(name,get_thm());
				_syntax->skip(";");
				cout << "lemma " << name << ": " << _syntax->pretty_thm(_loc.thm(name)) << endl;
			} else if( _syntax->skips("show") ) {
				string thm_name = _syntax->get_thm_name();
				_syntax->skip(":");
				auto stmt_loc = _loc.branch();
				CTerm stmt = stmt_loc.enclose(_syntax->get_term(0));
				cout << "Show " << thm_name << ": " << _syntax->pretty_term(stmt);
				if( _syntax->skips(",") ) {
					_syntax->skip("assuming");
					cout << ", assuming " << flush;
					for(;;) {
						string assm_name = _syntax->get_thm_name();
						_syntax->skip(":");
						Term term = _syntax->get_term(0);
						cout << assm_name << ": " << _syntax->pretty_term(term) << flush;
						stmt_loc.assume(assm_name,term);
						if( !_syntax->skips(",") ) {
							break;
						}
						cout << ", " << flush;
					}
				}
				cout << endl;
				_syntax->skip(";");
				auto const& thm = prove(stmt_loc,stmt).loop();
				if( !thm ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				_loc.add_thm(thm_name,thm->intro());
			} else if( _syntax->skips("obtain") ) {
				string sym = _syntax->get_token();
				_syntax->skip("where");
				auto specs = get_named_terms();
				_syntax->skip(";");
				cout << "Obtaining " << sym << " where ";
				vector<string> names;
				for( auto& [name,spec] : specs ) {
					names.push_back(name);
					cout << name << ": " << _syntax->pretty_term(spec) << ", ";
				}
				Ctxt thesis_ctxt = _loc.branch();
				CTerm thesis = thesis_ctxt.fix(avoid("thesis",[&](auto x){
					return _loc.constant(x);
				}));
				Ctxt spec_ctxt = thesis_ctxt.branch();
				spec_ctxt.fix(sym);
				CTerm goal = thesis.weaken(spec_ctxt);
				for( auto& spec : ranges::reverse_view(specs) ) {
					goal = spec_ctxt.cterm(spec.second) >>= goal;
				}
				goal = goal.lift();
				goal = thesis_ctxt.cterm(ALL)(goal) >>= thesis;
				goal = goal.lift();

				cout << endl << "Proving " << _syntax->pretty_term(goal) << endl;
				auto const& thm_opt = prove(_loc,goal).loop();
				if( !thm_opt ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				_loc.obtain(*thm_opt,names.begin());
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
				_definer->define(_loc,l,r,name);
				cout << "Defined " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _syntax->skips("unfold") ) {
				if( !_thesis ) {
					cerr << "No goal for \"unfold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0});
				_syntax->skip(";");
				cout << "unfold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else if( _syntax->skips("fold") ) {
				if( !_thesis ) {
					cerr << "No goal for \"fold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0},true);
				_syntax->skip(";");
				cout << "fold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else if( _syntax->skips("by") ) {
				if( !_thesis ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm const& thm = get_thm().intro();
				_syntax->skip(";");
				CTerm stmt = _thesis->capp()->first.capp()->second;
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
							CTerm cong_pat = _loc.branch().enclose(get_term());
							_syntax->skip(":");
							Thm const& cong_thm = get_thm();
							rewriter.register_quantifier_cong(cong_pat,cong_thm);
							cout << "\tquantifier [" << _syntax->pretty_term(cong_pat) <<
								 "] " << _syntax->pretty_thm(cong_thm) << endl;
						} else {
							CTerm cong_pat = _loc.branch().enclose(get_term());
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
				Thm ret = sorry(_thesis->capp()->second);
				cerr << "!!! SORRY !!! " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else {
				return Opt<Thm>();
			}
		} catch ( Error const& e ) {
			cerr << "ERROR: " << _syntax->pretty_term(e.term) << endl;
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

