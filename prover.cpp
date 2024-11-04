#include<fstream>
#include<ranges>
#include"locale.hpp"
#include"parser.hpp"
#include"definer.hpp"
#include"concluder.hpp"

using namespace std;

using ClaimStatus = pair<bool,Opt<string>>;
ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.second ) {
		os << *cs.second;
	}
	return os << ( cs.first ? "! " : ": " );
}

struct ProverFailure : exception {
	string message;
	ProverFailure(string const& message) : message(message) {}
};
class UnfinishedProof : exception {};

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
		_syntax->closer("}");
		_syntax->closer("]");
		_syntax->register_multi_op(int_of_chars("∀"));
		_syntax->register_multi_op(int_of_chars("⟹"));
		_syntax->register_single_op(',');
		_syntax->register_single_op(';');
		_syntax->register_multi_op(':');
		_syntax->register_multi_op('*');
		_syntax->register_multi_op('+');
		_syntax->infix(",",-1,-1,-2);
		_syntax->infix(";",-1,-1,-2);
		_syntax->infix(":",-1,-1,-2);
		_syntax->infix(":=",-1,-1,-2);
	}
	Prover prover(Locale const& loc, CTerm const& goal) {
		Ctxt ctxt = goal.ctxt().branch();
		Thm thesis = ctxt.assume(goal.weaken(ctxt)).intro();// goal ⟹ goal
		return Prover(*this,loc,thesis);
	}
	Opt<Thm> gets_thm() {
		auto loc = _loc.branch();
		if( auto const& thm = _gets_thm(loc) ) {
			return thm->intro();
		}
		return {};
	}
	Thm get_thm() {
		if( auto thm = gets_thm() ) {
			return *thm;
		}
		throw Parser::Error("expects a theorem");
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

	Opt<Thm> _gets_thm(Locale loc) {
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
	Prover& preproc() & {
		for(;;) {
			if( _syntax->skips("assuming") ) {
				cout << ", assuming " << flush;
				for(;;) {
					string assm_name = _syntax->get_thm_name();
					_syntax->skip(":");
					Term term = _syntax->get_term(0);
					cout << assm_name << ": " << _syntax->pretty_term(term) << flush;
					_loc.assume(assm_name,term);
					if( !_syntax->skips(",") ) {
						break;
					}
					cout << ", " << flush;
				}
				cout << endl;
			} else if( _syntax->skips("unfolding") ) {
				if( !_thesis ) {
					cerr << "No goal for \"unfold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0});
				_syntax->skip(";");
				cout << "unfold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else if( _syntax->skips("folding") ) {
				if( !_thesis ) {
					cerr << "No goal for \"fold\"" << endl;
					throw UnfinishedProof();
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0},true);
				_syntax->skip(";");
				cout << "fold: " << _syntax->pretty_thm(*_thesis) << endl;
			} else {
				break;
			}
		}
		return *this;
	}
	Prover&& preproc() && {
		return std::move(preproc());
	}
	ClaimStatus get_claim_status() {
		ClaimStatus ret;
		if( _syntax->skips("!") ) {
			if( !_thesis ) {
				cerr << "unexpected conclusion!" << endl;
				throw UnfinishedProof();
			}
			ret.first = true;
		} else {
			ret.second = _syntax->get_thm_name();
			if( _syntax->skips("!") ) {
				ret.first = true;
			} else {
				_syntax->skip(":");
				ret.first = false;
			}
		}
		return move(ret);
	}
	void add_claim( ClaimStatus cs, Thm const& thm ) {
		if( cs.first ) {
			conclude(thm);
		}
		if( cs.second ) {
			_loc.add_thm(*cs.second,thm);
		}
	}
	void conclude( Thm thm ) {
		Ctxt thesis_ctxt = _thesis->ctxt();
		// move the theorem up to the thesis context
		Thm arg = thm;
		while( arg.ctxt() != thesis_ctxt ) {
			arg = arg.intro();
		}
		CTerm goal = _thesis->capp()->first.capp()->second;
		Ctxt goal_vars = thesis_ctxt.branch();
		CTerm goal_strip = strip_all(goal,goal_vars);
		arg = arg.weaken(goal_vars);// arg will be instantiated with goal variables
		Ctxt arg_vars = goal_vars.branch();
		Thm arg_strip = strip_all(arg,arg_vars);
		Opt<CSubst> matcher = match(arg_vars.fvars(),arg_strip,goal_strip);
		if( !matcher ) {
			cout << "Proof mismatch: encountered " << _syntax->pretty_thm(arg) << 
", while expecting " << _syntax->pretty_cterm(goal) << endl;
			throw Error(Term("#proof-mismatch")(goal)(arg));
		}
		for( size_t i = 0; i < arg_vars.revision(); i++ ) {
			auto v = arg_vars.fixed(i);
			assert(v);
			arg = arg.allE(matcher->get(*v)->subst(goal_vars));
		}
		arg = arg.intro(); // now quantify the goal variables
		*_thesis = _thesis->impE(arg);
		cout << "Concluded " << _syntax->pretty_thm(arg) << endl;
	}
	Opt<Thm> loop() {
		for(;;) try {
			_indent();
			_flush();
			if( _syntax->skips("{") ) {
				Locale loc = _loc.branch("");
				cout << "Creating context " << loc.id() << endl;
				Prover(*this,loc,{}).loop();
				_syntax->skip("}");
				cout << "Leaving context." << endl;
			} else if( _syntax->skips("locale") ) {
				string name = _syntax->get_token();
				cerr << "Creating locale " << name << endl;
				if( _syntax->skips("{") ) {
					Prover(*this,_loc.branch(name),{}).loop();
					_syntax->skip("}");
				} else {
					_syntax->skip(";");
				}
				cout << "end" << endl;
			} else if( _syntax->skips("import") ) {
				string prefix;
				string name = _syntax->get_token();
				if( _syntax->skips(":") ) {
					prefix = name;
					name = _syntax->get_token();
				}
				cerr << "interpreting " << prefix << ": " << name << endl;
				auto loc = _loc.locale(name);
				auto& intp = _loc.import(prefix,loc);
				for(;;) {
					auto t = _syntax->gets_term(1000);
					if( !t ) {
						break;
					}
					auto fix = intp.fixing();
					if( !fix ) {
						throw Error(Term{"#unexpected-instantiation"}(*t));
					}
					intp.instantiate( *t == "_" ? _loc.fix(*fix) : _loc.cterm(*t) );
				}
				for(;;) {
					auto fix = intp.fixing();
					if( !fix ) {
						break;
					}
					auto t = _loc.fixes(*fix);
					intp.instantiate( t ? *t : _loc.fix(*fix) );
				}
				if( _syntax->skips(",") ) {
					for(;;){
						if( _syntax->skips("discharge") ) {
							auto assm = intp.assuming();
							if( !assm ) {
								throw Error("#unexpected-discharge");
							}
							_indent();
							cerr << "discharging " << _syntax->pretty_cterm(*assm) << endl;
							Locale loc = _loc.branch();
							auto thm = prover(loc,*assm).loop();
							intp.discharge(*thm);
							continue;
						}
						if( _syntax->skips("admit") ) {
							auto assm = intp.assuming();
							if( !assm ) {
								throw Error("#unexpected-admit");
							}
							intp.discharge(_loc.Ctxt::assume(*assm));
							continue;
						}
						if( _syntax->skips("retain") ) {
							auto obtain = intp.obtaining();
							if( !obtain ) {
								throw Error("#unexpected-retain");
							}
							auto term = _syntax->get_term();
							CTerm specs = obtain->cbinder(ALL)->second;
							vector<Thm> thms;
							for(;;) {
								auto imp = specs.cbinary(IMP);
								if( !imp ) {
									break;
								}
								Locale loc = _loc.branch();
								CTerm spec = imp->first.weaken(loc);
								thms.push_back(prover(loc,spec).loop()->intro());
								specs = imp->second;
							}
							intp.retain(_loc.cterm(term),thms);
							continue;
						}
						break;
					}
					_syntax->skip("end");
				} else {
					_syntax->skip(";");
				}
				import_all(intp);
			} else if( _syntax->skips("ctxt") ) {
				string name = _syntax->get_token();
				_syntax->skip(";");
				cout << _loc.locale(name).pretty(*_syntax) << endl;
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
					_loc.assume(name,term);
					cout << name << ": " << _syntax->pretty_thm(_loc.thm(name)) << flush;
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
			} else if( _syntax->skips("note") ) {
				auto cs = get_claim_status();
				auto const& thm = get_thm();
				cout << "noting " << cs << _syntax->pretty_thm(thm) << endl;
				add_claim(cs,thm);
				_syntax->skip(";");
			} else if( _syntax->skips("show") ) {
				auto cs = get_claim_status();
				auto stmt_loc = _loc.branch();
				CTerm stmt = stmt_loc.enclose(_syntax->get_term(0));
				cout << "Showing " << cs << _syntax->pretty_term(stmt) << endl;
				if( _syntax->skips(",") ) {// may modify the statement locale
					prover(stmt_loc,stmt).preproc();
				}
				_syntax->skip(";");
				auto const& thm = prover(stmt_loc.branch(),stmt).loop()->intro();
				add_claim(cs,thm);
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
				auto thesis_loc = _loc.branch();
				CTerm thesis = thesis_loc.fix(avoid("thesis",[&](auto x){
					return _loc.constant(x);
				}));
				Ctxt spec_ctxt = thesis_loc.Ctxt::branch();
				spec_ctxt.fix(sym);
				CTerm goal = thesis.weaken(spec_ctxt);
				for( auto& spec : ranges::reverse_view(specs) ) {
					goal = spec_ctxt.cterm(spec.second) >>= goal;
				}
				goal = goal.lift();
				goal = thesis_loc.cterm(ALL)(goal) >>= thesis;
				cout << endl;
				_indent();
				cout << "Prove " << _syntax->pretty_cterm(goal) << endl;
				auto const& thm = prover(thesis_loc.branch(),goal).loop()->intro();
				_loc.obtain(thm,names.begin());
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
				auto [f,thm] = _definer->define(_loc,l,r);
				_loc.add_thm( name ? *name : f + "_def", thm );
				cout << "Defined " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _syntax->skips("by") ) {
				if( !_thesis ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm const& thm = get_thm();
				_syntax->skip(";");
				conclude(thm);
				return _thesis;
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
					cout << "Adding concluder: ";
					while( auto thm = gets_thm() ) {
						cout << _syntax->pretty_thm(*thm);
						_concluder.insert(*thm);
						cout << "\t" << *thm << endl;
					}
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
				cerr << "registering symbols" << flush;
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
			cerr << _syntax->line_counter() << "ERROR: " << _syntax->pretty_term(e.term) << endl;
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
//			_syntax.fork();
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

