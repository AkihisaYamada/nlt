#include<fstream>
#include<ranges>
#include"locale.hpp"
#include"parser.hpp"
#include"definer.hpp"
#include"concluder.hpp"

using namespace std;

struct ClaimStatus {
	bool is_goal;
	Opt<string> name;
	ClaimStatus( string_view const& name, bool is_goal = false ) : is_goal(is_goal), name(in_place,name) {}
	ClaimStatus() : is_goal(true), name() {}
};
ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.name ) {
		os << *cs.name;
	}
	return os << ( cs.is_goal ? "! " : ": " );
}

fstream file_of_locale( string dir, string_view const& name ) {
	return fstream(dir+name+".nl");
}

Ref<Syntax> make_syntax() {
	auto ret = Ref<Syntax>::make();
	ret->register_multi_op(int_of_chars("∀"));
	ret->register_multi_op(int_of_chars("⟹"));
	ret->register_single_op(',');
	ret->register_single_op(';');
	ret->register_multi_op(':');
	ret->register_multi_op('*');
	ret->register_multi_op('+');
	ret->encloser("(",")",-1000,[&]( Parser& parser ){
		Opt<Term> t = parser.gets_term(0);
		parser.skip(")");
		return *t;
	});
	ret->closer("}");
	ret->closer("]");
	ret->infix(",",-1,-1,-2);
	ret->infix(";",-1,-1,-2);
	ret->infix(":",-1,-1,-2);
	ret->infix(":=",-1,-1,-2);
	ret->prefix("if",-3,-2);
	ret->infix("then",-3,-2,-2);
	return ret;
}

static Error const ProofMismatch = Error("#proof-mismatch");

class Prover {
	Opt<Ref<Prover>> _parent;
	unsigned int _depth;
	Locale _loc;
	struct Path {
		string dir;
		string name;
		Path( string_view const& dir, string_view const& name ) : dir(dir), name(name) {}
	};
	Opt<Path> _path;
	bool _own_parser;
	Ref<Syntax> _syntax;
	Parser _parser;
	Opt<Thm> _thesis;
	Concluder _concluder;
	StrMap<Ref<Rewriter>> _rewriters;
	OptRef<Definer> _definer;
	bool _exit_on_error;
	Prover(Prover& parent, Locale const& loc, Opt<Path> const& path, Opt<Thm> thesis = {}) :
		_parent(Ref<Prover>::make(parent)),
		_depth(parent._depth+1),
		_loc(loc),
		_path(path),
		_syntax(parent._syntax),
		_parser(parent._parser.get_lexer(),*parent._syntax),
		_own_parser(false),
		_thesis(thesis),
		_concluder(parent._concluder),
		_rewriters(parent._rewriters),
		_definer(parent._definer),
		_exit_on_error(parent._exit_on_error) {
		_prompt();
	}
	void _error() {
		if( _exit_on_error ) {
			exit(-1);
		}
	}
public:
	struct Error : ::Error {
		static inline Term const RT = Term("#prover_error");
		Error( Term const& msg ) : ::Error(RT(msg)) {
		}
	};
	Prover( Lexer& lexer, Ref<Syntax> syntax, bool exit_on_error ) :
		_depth(0),
		_path({"","Root"}),
		_loc(),
		_syntax(syntax),
		_parser(lexer,*_syntax),
		_own_parser(true),
		_exit_on_error(exit_on_error) {
		_prompt();
	}
	void set_exit_on_error( bool b ) {
		_exit_on_error = b;
	}
	Prover branch( string_view const& name ) {
		auto loc = _loc.branch(name);
		if( _path ) {
			return Prover( *this, loc, {{_path->dir+"/"+_path->name,name}});
		} else {
			return Prover( *this, loc, {}, {} );
		}
	}
	Lexer const& get_lexer() const {
		return _parser.get_lexer();
	}
	void set_lexer( Lexer& lexer ) {
		_parser.set_lexer(lexer);
	}
	Thm prove(Locale const& loc, CTerm const& goal) {
		Ctxt ctxt = goal.ctxt().branch();
		Thm thesis = ctxt.assume(goal.weaken(ctxt)).intro();// goal ⟹ goal
		return Prover(*this,loc,{},thesis).proof_loop();
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
		if( _parser.skips("[") ) {
			name = _parser.get_token();
			_parser.skip("]");
		}
		auto const& p = _rewriters.finds(name);
		if( !p ) {
			throw Error("#rewriter_not_found");
		}
		return p->second;
	}
	Thm _rewrite( Rewriter const& rewriter, Locale& loc, Thm const& source, vector<char> pos, bool rev = false ) {
		if( _parser.skips("(") ) {
			while( !_parser.skips(")") ) {
				pos.push_back(_parser.get_int());
			}
		}
		unsigned int min, max;
		if( _parser.skips("*") ) {
			min = 0; max = 255;
		} else if( _parser.skips("+") ) {
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
		auto const& opt = _parser.gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = loc.thm(*opt);
		for(;;) {
			if( _parser.skips("(") ) {
				do {
					ret = ret.allE(loc.enclose(_parser.get_term()));
				} while( _parser.skips(",") );
				_parser.skip(")");
			} else if( _parser.skips("[") ) {
				if( _parser.skips("OF") ) {
					while( auto const& arg = _gets_thm(loc) ) {
						ret = discharge(ret,*arg);
					}
				} else if( _parser.skips("unfolded") ) {
					auto const& rewriter = *_rewriter();
					ret = _rewrite(rewriter,loc,ret,{},false);
				} else if( _parser.skips("folded") ) {
					auto const& rewriter = *_rewriter();
					ret = _rewrite(rewriter,loc,ret,{},true);
				}
				_parser.skip("]");
			} else {
				return ret;
			}
		}
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		while( auto const& name = _parser.gets_thm_name() ) {
			_parser.skip(":");
			Thm const& thm = get_thm();
			ret.insert({*name,thm});
		}
		return ret;
	}
	Opt<Term> gets_term() {
		if( auto const& term = _parser.gets_term() ) {
			Term ret = *term;
			if( _parser.skips("$") ) {
				CSubst subst = _loc.branch();
				do {
					string sym = _parser.get_token();
					_parser.skip(":=");
					subst.assign(sym,get_term());
				} while( _parser.skips(",") );
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

	void get_named_terms( function<void(string const&, Term const&)> const& f ) {
		for(;;) {
			auto const& name = _parser.gets_thm_name();
			if(!name) {
				return;
			}
			_parser.skip(":");
			f(*name,_parser.get_term(0));
			if( !_parser.skips(",") ) {
				return;
			}
		}
	}

	void _flush() {
		cout << flush;
	}
	ostream& _indent() {
		for( int i = 0; i <= _depth; i++ ) {
			cout << '>';
		}
		return cout << ' ';
	}
	void _prompt() {
		_indent() << flush;
	}
	Opt<CTerm> has_goal() {
		if( _thesis )
		if( auto bin = _thesis->cbinary(IMP) )
			return bin->first;
		return {};
	}
	Thm proof_loop() {
		for(;;) {
			if( _parser.skips("apply") ) {
				if( !_thesis ) {
					throw Error("\"No goal for apply\"");
				}
				auto rule = get_thm();
				auto res = rule_applies(rule,*_thesis);
				if( !res ) {
					throw Error("\"Rule not applicable\"")(rule)(*_thesis);
				}
				*_thesis = *res;
				if( auto g = has_goal() ) {
					cout << "applied goal: " << _syntax->pretty_cterm(*g) << endl;
				} else {
					cout << "no subgoal!" << endl;
				}
			} else if( _parser.skips("unfold") ) {
				if( !_thesis ) {
					throw Error("\"No goal for unfold\"");
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0});
				auto g = has_goal();
				assert(g);
				cout << "unfolded goal: " << _syntax->pretty_cterm(*g) << endl;
			} else if( _parser.skips("fold") ) {
				if( !_thesis ) {
					throw Error("\"No goal for fold\"");
				}
				Rewriter const& rewriter = *_rewriter();
				*_thesis = _rewrite(rewriter,_loc,*_thesis,{0},true);
				auto g = has_goal();
				assert(g);
				cout << "folded goal: " << _syntax->pretty_cterm(*g) << endl;
			} else {
				break;
			}
			_parser.skip(";");
			_prompt();
		}
		_loc = _loc.branch();
		auto thm = loop();
		if( !thm ) {
			throw Error("\"missing conclusion\"");
		}
		return *thm;
	}
	ClaimStatus get_claim_status() {
		bool is_goal;
		if( _parser.skips("!") ) {
			if( !_thesis ) {
				throw Error("\"unexpected conclusion\"");
			}
			return {};
		} else {
			auto name = _parser.get_thm_name();
			if( _parser.skips("!") ) {
				return {name,true};
			} else {
				_parser.skip(":");
				return {name,false};
			}
		}
	}
	void add_claim( ClaimStatus cs, Thm const& thm ) {
		if( cs.is_goal ) {
			conclude(thm);
		}
		if( cs.name ) {
			_loc.add_thm(*cs.name,thm);
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
		Opt<CSubst> matcher = match(arg_vars.fvars(),arg_strip,goal_strip.weaken(arg_vars));
		if( !matcher ) {
			throw ProofMismatch(goal_strip)(arg_strip);
		}
		// instantiate arg variables
		auto intp = Intp::make(arg_vars,goal_vars);
		for( size_t i = 0; i < arg_vars.revision(); i++ ) {
			auto v = arg_vars.fixed(i);
			assert(v);
			auto val = matcher->get(*v);
			intp.instantiate( val ? val->csubst(goal_vars) : goal_vars.cterm("_"/=Term("_"))/* dummy */ );
		}
		Thm inst = intp.subst(arg_strip);
		// quantify the goal variables
		inst = inst.intro();
		*_thesis = _thesis->impE(inst);
	}
	Locale find_locale( string_view const& name ) {
		auto loc = _loc.find_locale(name);
		if( !loc ) {
			load_locale(name);
			loc = _loc.find_locale(name);
		}
		if( !loc ) {
			throw Error((string("\"unknown locale ") += name) + "\"");
		}
		return *loc;
	}
	Opt<Thm> loop() {
		for(;;) try {
			if( _parser.skips("{") ) {
				Locale loc = _loc.branch("");
				cout << "Creating context " << loc.id() << endl;
				Prover(*this,loc,{},{}).loop();
				_parser.skip("}");
				cout << "Leaving context." << endl;
			} else if( _parser.skips("locale") ) {
				string name = _parser.get_token();
				cout << "Creating locale " << name << endl;
				if( _parser.skips("{") ) {
					Prover(*this,_loc.branch(name),{},{}).loop();
					_parser.skip("}");
				} else {
					_parser.skip(";");
				}
				cout << "ending locale " << name << endl;
			} else if( _parser.skips("import") ) {
				string prefix;
				string name = _parser.get_token();
				if( _parser.skips(":") ) {
					prefix = name;
					name = _parser.get_token();
				}
				bool has_mod = _parser.skips("{") || (_parser.skip(";"), false);
				auto loc = find_locale(name);
				auto& intp = _loc.import(prefix,loc);
				if( has_mod ) {
					cout << "importing " << name << endl;
					_depth++;
					for(;;){
						if( auto v = intp.fixing() ) {
							cout << "Instantiate " << *v << endl;
							_indent();
							if( _parser.skips("for") ) {
								if( _parser.skips("_") ) {
									assert( intp.instantiates() );
								} else {
									auto t = _parser.get_term();
									intp.instantiate(_loc.enclose(t));
									cout << "for " << _syntax->pretty_term(t) << endl;
								}
								_parser.skip(";");
							}
						} else if( auto assm = intp.assuming() ) {
							cout << "Discharge " << _syntax->pretty_cterm(*assm) << endl;
							_indent();
							if( _parser.skips("discharge") ) {
								Locale loc = _loc.branch();
								intp.discharge(prove(loc,*assm));
							} else if( _parser.skips("assume") ) {
								_parser.skip(";");
								Thm thm = _loc.Ctxt::assume(*assm);
								intp.discharge(thm);
								cout << "Assumed " << _syntax->pretty_thm(thm) << endl;
							} else {
								break;
							}
						} else if( auto obtain = intp.obtaining() ) {
							auto [sym,thm,spec] = *obtain;
							cout << "Obtain " << sym << " in " << _syntax->pretty_cterm(spec) << endl;
							_indent();
							if( _parser.skips("obtain") ) {
								if( _parser.skips(";") ) {
								} else {
									sym = _parser.get_token();
									_parser.skip(";");
								}
								auto [sym_term,spec] = _loc.obtain(sym,thm);
								intp.retain(sym_term,spec);
							} else if( _parser.skips("for") ) {
								Locale thesis_loc = _loc.branch();
								auto term = thesis_loc.cterm(_parser.get_term());
								_parser.skip(";");
								CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
									return _loc.constant(x);
								}));
								CTerm t = thm.capp()->second;
// var'. (∀sym. props... ⟹ var') ⟹ var'
								t = t.weaken(thesis_loc).inst(var);
// (∀sym. props... ⟹ var) ⟹ var
								t = t.cbinary(IMP)->first;
// ∀sym. props... ⟹ var
								t = t.capp()->second.inst(term);
// props[sym:=term]... ⟹ var
// assume this
								Thm rule = thesis_loc.Ctxt::assume(t);
// and prove var, i.e., props[sym:=term]...
								Thm thesis = make_refl(var);
								auto thesis2 = rule_applies(rule,thesis);
								if( !thesis2 ) {
									throw Error(rule)(thesis);
								}
								auto spec = Prover(*this,thesis_loc,{},{thesis2}).proof_loop().intro();
// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
								intp.retain(_loc.cterm(term),spec);
							} else {
								break;
							}
						} else {
							cout << "Complete!" << endl;
							_indent();
							break;
						}
					}
					_parser.skip("}");
					_depth--;
				}
				while( intp.instantiates() || intp.discharges() || intp.retains() );
				if( !has_mod ) {
					cout << "imported " << name << endl;
				}
			} else if( _parser.skips("ctxt") ) {
				if( _parser.skips(";") ) {
					if( _path ) {
						cout << _path->name << ": ";
					}
					cout << _loc.pretty(*_syntax) << endl;
				} else {
					string name = _parser.get_token();
					_parser.skip(";");
					cout << _loc.locale(name).pretty(*_syntax) << endl;
				}
			} else if( _parser.skips("fix") ) {
				cout << "Fixing";
				while( !_parser.skips(";") ) {
					cout << ' ' << _loc.fix(_parser.get_token()) << flush;
				}
				cout << ';' << endl;
			} else if( _parser.skips("assume") ) {
				cout << "Assuming ";
				get_named_terms([&](string const& s, Term const& t){
					_loc.assume(s,_loc.Ctxt::branch().enclose(t).lift(_loc.cterm(ALL)));
					cout << s << ": " << _syntax->pretty_thm(_loc.thm(s)) << "; " << flush;
				});
				_parser.skip(";");
				cout << endl;
			} else if( _parser.skips("thm") ) {
				Thm thm = get_thm();
				_parser.skip(";");
				cout << "thm " << _syntax->pretty_thm(thm) << endl;
			} else if( _parser.skips("goal") ) {
				_parser.skip(";");
				if( auto g = has_goal() ) {
					cout << "goal: " << _syntax->pretty_cterm(*g) << endl;
				} else {
					cout << "no goal" << endl;
				}
			} else if( _parser.skips("term") ) {
				Term term = get_term();
				_parser.skip(";");
				cout << "term " << _syntax->pretty_term(term) << endl;
			} else if( _parser.skips("note") ) {
				auto cs = get_claim_status();
				auto const& thm = get_thm();
				cout << "noting " << cs << _syntax->pretty_thm(thm) << endl;
				add_claim(cs,thm);
				_parser.skip(";");
			} else if( _parser.skips("show") ) {
				auto cs = get_claim_status();
				cout << "Showing " << cs << flush;
				auto goal_loc = _loc.branch();
				vector<pair<string,CTerm>> assms;// delay making assumptions, so that all free variables are fixed first
				if( _parser.skips("for") ) {
					while( !_parser.skips(",") ) {
						goal_loc.fix(_parser.get_token());
					}
				}
				if( _parser.skips("if") ) {
					cout << "if " << flush;
					get_named_terms([&](string const& s, Term const& t){
						cout << s << ": " << _syntax->pretty_term(t) << ", " << flush;
						assms.emplace_back(s,goal_loc.enclose(t));
					});
					_parser.skip("then");
					cout << "then ";
				}
				Term conc = _parser.get_term(0);
				_parser.skip(";");
				CTerm goal = goal_loc.enclose(conc);
				for( auto [name,assm] : assms ) {
					goal_loc.assume(name,assm);
				}
				cout << _syntax->pretty_cterm(goal) << endl;
				auto const& thm = prove(goal_loc,goal);
				if( goal != thm ) {
					throw ProofMismatch(thm)(goal);
				}
				add_claim(cs,thm.intro());
			} else if( _parser.skips("obtain") ) {
				string sym = _parser.get_token();
				_parser.skip("where");
				cout << "Obtaining " << sym << " where ";
				vector<string> names;
				vector<Term> props;
				get_named_terms([&]( string const& s, Term const& t ) {
					names.push_back(s);
					props.push_back(t);
					cout << s << ": " << _syntax->pretty_term(t) << ", ";
				});
				_parser.skip(";");
				auto thesis_loc = _loc.branch();
				CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
					return _loc.constant(x);
				}));
				Ctxt spec_ctxt = thesis_loc.Ctxt::branch();
				spec_ctxt.fix(sym);
				CTerm goal = var.weaken(spec_ctxt);
				for( auto& prop : ranges::reverse_view(props) ) {
					goal = spec_ctxt.cterm(prop) >>= goal;
				}
				goal = goal.lift(thesis_loc.cterm(ALL)) >>= var;
				goal = goal.lift(_loc.cterm(ALL));
				cout << endl;
				_indent();
				cout << "Prove " << _syntax->pretty_cterm(goal) << endl;
				auto const& thm = prove(_loc.branch(),goal);
				auto [sym_term,spec] = _loc.obtain(sym,thm);
				// register properties
				auto all = spec.cbinder(ALL);
				assert(all);
				auto imp = all->second.cbinary(IMP);
				assert(imp);
				auto subst = CSubst(spec.ctxt());// to remove thesis
				auto name_it = names.begin();
				Thm refl = _loc.thm("imp.refl");// P ⟹ P
				Thm weaken = _loc.thm("weaken");// (P ⟹ Q) ⟹ P
				Thm ignore = _loc.thm("ignore");// ((P ⟹ Q) ⟹ R) ⟹ Q ⟹ R
				CTerm s = imp->first;// P ⟹ props ⟹ var
				auto imp2 = s.cbinary(IMP);
				auto prop = imp2->first;// P
				s = imp2->second;// props... ⟹ var
				for(;;) {
					if( auto imp3 = s.cbinary(IMP) ) {// more props follow
						s = imp2->second;// props... ⟹ var
						add_claim( ClaimStatus(*name_it), spec << weaken );// P
						spec = ignore << spec;// ∀var. (props... ⟹ var) ⟹ var
						name_it++;
					} else {// spec: ∀var. (P ⟹ var) ⟹ var
						add_claim( ClaimStatus(*name_it), spec << refl );// P
						break;
					}
				}
				cout << "Obtained " << sym << endl;
			} else if( _parser.skips("define") ) {
				Opt<string> name;
				if( _parser.skips("(") ) {
					name = _parser.get_token();
					_parser.skip(")");
				}
				Term l = get_term();
				_parser.skip(":=");
				Term r = get_term();
				_parser.skip(";");
				if( !_definer ) {
					throw Error("definer not setup");
				}
				auto [f,spec] = _definer->define(_loc,l,r);
				Thm def = spec << _loc.thm("imp.refl");
				_loc.add_thm( name ? *name : f + "_def", def );
				cout << "Defined " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _parser.skips("by") ) {
				if( !_thesis ) {
					throw Error("No goal for \"by\"");
				}
				Thm const& thm = get_thm();
				_parser.skip(";");
				conclude(thm);
				cout << "Concluded " << _syntax->pretty_thm(*_thesis) << endl;
				return _thesis;
			} else if( _parser.skips("done") ) {
				if( !_thesis ) {
					throw Error("No goal for \"done\"");
				}
				_parser.skip(";");
				cout << "Done." << endl;
				return _concluder.conclude(*_thesis);
			} else if( _parser.skips("qed") ) {
				_parser.skip(";");
				if( !_thesis ) {
					throw Error("No goal for \"qed\"");
				}
				cout << "QED" << endl;
				return _thesis;
			} else if( _parser.skips("prefix") ) {
				string sym = _parser.get_token();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(";");
				_make_own_parser();
				_syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( _parser.skips("infix") ) {
				string sym = _parser.get_token();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(";");
				_make_own_parser();
				_syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else if( _parser.skips("setup") ) {
				if( _parser.skips("conclude") ) {
					cout << "Adding concluder:" << endl;
					while( auto thm = gets_thm() ) {
						cout << '\t' << _syntax->pretty_thm(*thm) << endl;
						_concluder.insert(*thm);
					}
				} else if( _parser.skips("rewrite") ) {
					string name;
					if( _parser.skips("[") ) {
						name = _parser.get_token();
						_parser.skip("]");
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
				} else if( _parser.skips("cong") ) {
					Rewriter& rewriter = *_rewriter();
					cout << "Registering Congruence:" << endl;
					for(;;) {
						if( _parser.skips("!") ) {
							CTerm cong_pat = _loc.branch().enclose(get_term());
							_parser.skip(":");
							Thm const& cong_thm = get_thm();
							rewriter.register_quantifier_cong(cong_pat,cong_thm);
							cout << "\tquantifier [" << _syntax->pretty_term(cong_pat) <<
								 "] " << _syntax->pretty_thm(cong_thm) << endl;
						} else {
							CTerm cong_pat = _loc.branch().enclose(get_term());
							_parser.skip(":");
							Thm const& cong_thm = get_thm();
							rewriter.register_cong(cong_pat,cong_thm);
							cout << "\t[" << _syntax->pretty_term(cong_pat) <<
								 "] " << _syntax->pretty_thm(cong_thm) << endl;
						}
						if( !_parser.skips(",") ) {
							break;
						}
					}
				} else if( _parser.skips("define") ) {
					string const& eq = _parser.get_token();
					string const& lam = _parser.get_token();
					Thm const& beta = get_thm();
					cout << "equality: " << eq << " lambda: " << lam << " beta: " << _syntax->pretty_thm(beta) << endl;
					auto const& rewriter = _rewriters.find(string())->second;
					_definer = OptRef<Definer>::make(rewriter,eq,lam,beta);
				} else if( _parser.skips("set_comprehension") ) {
					Term const& empty = _parser.get_term(1000);
					Term const& singleton = _parser.get_term(1000);
					Term const& collect = _parser.get_term(1000);
					Term const& lam = _parser.get_term(1000);
					Term const& un = _parser.get_term(1000);
					auto handler = [=,*this](Parser& parser) {
						auto const& inner = parser.gets_term(0);
						if( !inner ) {
							parser.skip("}");
							return empty;
						}
						if( inner->abs() ) {
							parser.skip("}");
							return collect(lam(*inner));
						}
						Term ret = singleton(*inner);
						while( parser.skips(",") ) {
							auto const inner2 = parser.gets_term(0);
							ret = un(ret)(singleton(*inner2));
						}
						parser.skip("}");
						return ret;
					};
					_syntax->encloser("{","}",-1000,handler);
				} else if( _parser.skips("print") ) {
					if( _parser.skips("ctxt_id") ) {
						_syntax->print_ctxt(true);
					}
				}
				_parser.skip(";");
			} else if( _parser.skips("symbol") ) {
				bool solo = _parser.skips("solo");
				cout << "registering symbols";
				while( !_parser.skips(";") ) {
					string const& sym = _parser.get_token();
					int ch = int_of_chars(sym.data());
					if( solo ) {
						_syntax->register_single_op(ch);
					} else {
						_syntax->register_multi_op(ch);
					}
					cout << ' ' << sym;
				}
				cout << endl;
			} else if( _parser.skips("sorry") ) {
				_parser.skip(";");
				Thm ret = sorry(_thesis->capp()->second);
				cerr << "!!! SORRY !!! " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else if( _parser.skips("") || _parser.peek_token() == "}" ) {
				return Opt<Thm>();
			} else {
				throw Error(Term("unexpected")(_parser.get_token()));
			}
			_prompt();
		} catch ( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _syntax->pretty_term(e.term) << endl;
			_error();
		} catch( Parser::Error const& e ) {
			cerr << _parser.location() << ": Parse ERROR: " << e.message << endl;
			_error();
		} catch ( exception const& e ) {
			cerr << _parser.location() << ": Other exception: " << e.what() << endl;
			_error();
		}
	}
	void load_locale( string_view const& name ) {
		if( _path ) {
			string dir = _path->dir + _path->name + "/";
			auto fis = file_of_locale(dir,name);
			if( !fis.fail() ) {
				auto& prev = get_lexer();
				Lexer local_lexer(fis,dir+name,*_syntax);
				local_lexer.skip("base");
				auto parent_name = local_lexer.get_token();
				local_lexer.skip(";");
				cout << "Loading " << name << endl;
				Prover sub = Prover(*this,_loc.branch(name),{{dir,name}},{});
				sub.set_lexer(local_lexer);
				sub.loop();
				cout << "Loaded " << name << endl;
				return;
			}
		}
		if( _parent ) {
			(**_parent).load_locale(name);
		}
	}
private:
	void _make_own_parser() {
		if( !_own_parser ) {
//			_parser.fork();
			_own_parser = true;
		}
	}
};

Prover preload( Lexer& lexer, Ref<Syntax>& syntax, string_view const& name, bool exit_on_error ) {
	if( lexer.skips("base") ) {
		string const& base_name = lexer.get_token();
		lexer.skip(";");
		auto fis = file_of_locale("Root/",base_name);
		if( fis.fail() ) {
			cerr << "could not find base " << base_name << endl;
			exit(-1);
		}
		auto local_lexer = Lexer(fis,base_name,*syntax);
		Prover base = preload(local_lexer,syntax,base_name,true);
		base.loop();
		cout << "Loaded " << base_name << endl;
		Prover sub = base.branch(name);
		sub.set_lexer(lexer);
		sub.set_exit_on_error(exit_on_error);
		return sub;
	} else {
		return Prover(lexer,syntax,exit_on_error);
	}
}

int main(int argc, char* argv[]) {
	istream* pis;
	auto syntax = make_syntax();
	bool exit_on_error = false;
	if( argc == 1 ) {
		Lexer lexer(cin,"stdin",*syntax);
		preload(lexer,syntax,"stdin",false).loop();
	} else {
		string name = argv[1];
		auto fin = file_of_locale("",name);
		Lexer lexer(fin,name,*syntax);
		preload(lexer,syntax,name,true).loop();
	}
	cout << "bye!" << endl;
	return 0;
}

