#include<fstream>
#include<filesystem>
#include<ranges>
#include"inference.hpp"
#include"parser.hpp"
#include"definer.hpp"

#define _cout if(_out) cout

using namespace std;

struct ClaimStatus {
	Opt<string> name;
	bool weak = false, force = false, cong = false, followable = true;
};

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.name ) {
		os << *cs.name;
	}
	if( cs.force ) {
		os << '!';
	}
	if( cs.weak ) {
		os << '?';
	}
	return os << ": ";
}

pair<fstream,string> file_of_thy( string_view const& dir, string_view const& name ) {
	auto path = string(dir);
	path+=name;
	path+=".nl";
	return {fstream(path),std::move(path)};
}

void init_syntax( Syntax& syntax ) {
	syntax.register_multi_op(int_of_chars("∀"));
	syntax.register_multi_op(int_of_chars("⟹"));
	syntax.register_single_op(',');
	syntax.register_single_op(';');
	syntax.register_multi_op(':');
	syntax.register_multi_op('=');
	syntax.register_multi_op('!');
	syntax.register_multi_op('?');
	syntax.register_multi_op('*');
	syntax.register_multi_op('+');
	syntax.register_multi_op('-');
	syntax.register_multi_op('#');
	syntax.opener("(",-1000,[&]( Parser& parser ){
		Opt<Term> t = parser.gets_term(-1000);
		parser.skip(")");
		return *t;
	});
	syntax.closer(")");
	syntax.closer("}");
	syntax.closer("]");
	syntax.infix(",",-2,-2,-3);
	syntax.infix(";",-3,-3,-4);
	syntax.infix(":=",-1,-1,-2);
	syntax.prefix("if",-1,-2);
	syntax.infix("then",-2,-1,-2);
	syntax.infix("else",-2,-2,-1);
}

static Error const ProofMismatch = Error("#proof-mismatch");

static void _read(Thy&,Parser&);

class Prover {
	unsigned int _depth;
	Thy _thy;
	Parser& _parser;
	bool _exit_on_error;
	bool _final = false;
	bool _out = true;
	bool _out_load = false;
	Prover( Prover& parent, Thy const& loc ) :
		_depth(parent._depth),
		_thy(loc),
		_parser(parent._parser),
		_exit_on_error(parent._exit_on_error),
		_out(parent._out),
		_out_load(parent._out_load) {
	}
public:
	struct Error : ::Error {
		static inline Term const RT = Term("#prover_error");
		Error( Term const& msg ) : ::Error(RT(msg)) {
		}
	};
	Prover( Thy const& thy, Parser& parser, bool exit_on_error ) :
		_depth(0),
		_thy(thy),
		_parser(parser),
		_exit_on_error(exit_on_error) {
		_prompt();
	}
	Thy& thy() & {
		return _thy;
	}
	Prover& deepen() & {
		_depth++;
		_prompt();
		return *this;
	}
	Prover&& deepen() && {
		_depth++;
		_prompt();
		return std::move(*this);
	}
	void enter_branch( string_view const& name, string_view const& dirname ) {
		_thy = _thy.branch(name,dirname).thy();
		_final = false;
	}
	void set_exit_on_error( bool b ) {
		_exit_on_error = b;
	}
	void set_out( bool out, bool out_load ) {
		_out = out;
		_out_load = out_load;
	}
	Lexer& get_lexer() & {
		return _parser.get_lexer();
	}
	void set_lexer( Lexer& lexer ) {
		_parser.set_lexer(lexer);
	}
	Opt<Thm> gets_thm() {
		auto loc = _thy.branch();
		if( auto const& thm = _gets_thm(loc) ) {
			return thm->intro();
		}
		return {};
	}
	Thm get_thm() {
		auto ret = gets_thm();
		if( !ret ) throw Parser::Error("expects a theorem");
		return *ret;
	}
	pair<Rewriter::Rules,Rewriter::Ctrl> _get_rewrite( Import const& loc, bool rev = false ) {
		pair<Rewriter::Rules,Rewriter::Ctrl> ret = {_thy.rewriter().make_rules(),{}};
		auto& [rules,ctrl] = ret;
		if( _parser.skips("(") ) {
			ctrl.rel = _parser.get();
			_parser.skip(")");
		}
		if( _parser.skips("[") ) {// parse position
			while( !_parser.skips("]") ) {
				ctrl.pos.push_back(_parser.get_int());
			}
		}
		if( _parser.skips("*") ) {
			ctrl.min = 0; ctrl.max = 255; ctrl.safe = false;
		} else if( _parser.skips("+") ) {
			ctrl.min = 1; ctrl.max = 255; ctrl.safe = false;
		} else {
			ctrl.min = 1; ctrl.max = 1; ctrl.safe = true;
		}
		size_t n = 0;
		while( auto const& arg = _gets_thm(loc) ) {
			_thy.rewriter().add_rule( loc.thy(), rules, *arg, _parser.skips("-") ? !rev : rev );
			n++;
		}
		if( ctrl.max < n ) {
			ctrl.max = n;
		}
		return ret;
	}
	Opt<Thm> _gets_thm( Import const& loc ) {
		auto const& opt = _parser.gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = loc.thy().thm(*opt);
		if( _parser.skips("[") ) {
			for(;;) {
				if( _parser.skips("of") ) {
					while( auto t = _parser.gets_term(1000) ) {
						ret = ret.instantiate(loc.thy().enclose(*t));
					}
				} else if( _parser.skips("OF") ) {
					for(;;) {
						if( _parser.skips("!") ) {
							ret = blast(ret,loc.thy());
						} else if( _parser.skips("_") ) {
							auto imp = ret.cbinary(IMP);
							if( !imp ) throw Error("\"no premise for _\"");
							ret = discharge(ret,loc.thy().assume(imp->first));
						} else if( auto const& arg = _gets_thm(loc) ) {
							ret = discharge(ret,*arg);
						} else {
							break;
						}
					}
				} else if( _parser.skips("THEN") ) {
					auto thm = get_thm();
					auto [strip_thm,tmp,n] = strip_all(thm);
					auto imp = strip_thm.cbinary(IMP);
					if( !imp ) throw Error("\"malformed THEN\"")(strip_thm);
					auto cond = imp->first;
					auto arg = ret.subst(tmp);
					for(;;){
						arg = strip_all(arg,tmp).first;
						auto imp = arg.cbinary(IMP);
						if( !imp ) break;
						arg = arg.discharge(tmp.ctxt().assume(imp->first));
					}
					auto u = unify(arg,cond,[&](auto v){ return tmp.ctxt().fixes(v); });
					if( !u ) throw Error("\"mismatching THEN\"")(arg)(strip_thm);
					auto intp = Intp::make(tmp.ctxt(),loc.ctxt()).compose(loc);
					for(;;){
						if( auto const& v = intp.fixing() ) {
							intp.instantiate(loc.thy().enclose( [&]()->Term{
								if( auto t = u->get(*v) ) return *t;
								return *v;
							}()));
						} else if( auto const& assm = intp.assuming() ) {
							intp.discharge(loc.thy().assume(loc.thy().cterm(*assm)));
						} else {
							break;
						}
					}
					thm = strip_thm.subst(intp);
					ret = thm.discharge(arg.subst(intp));
				} else if( _parser.skips("for") ) {
					while( auto x = _parser.gets(Lexer::Word) ) {
						loc.thy().fix(*x);
					}
				} else if( bool dir = false; _parser.skips("unfolded") || (dir = true, _parser.skips("folded")) ) {
					auto [rules,ctrl] = _get_rewrite(loc,dir);
					ret = _thy.rewriter().rewrite(rules,loc.thy(),ret,ctrl);
				} else break;
				if( !_parser.skips(",") ) break;
			}
			_parser.skip("]");
		}
		return ret;
	}
	Thm _get_thm( Import& loc ) {
		auto ret = _gets_thm(loc);
		if( !ret ) throw Parser::Error("expects a theorem");
		return *ret;
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
				Subst subst = _thy.branch();
				do {
					string sym = _parser.get();
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
	Opt<string> gets_sym() {
		if( _parser.skips("(") ) {
			auto const& ret = _parser.get();
			_parser.skip(")");
			return ret;
		} else {
			return _parser.gets(Tokenizer::Word);
		}
	}
	string get_sym() {
		auto ret = gets_sym();
		if( ret ) return *ret;
		throw Error("\"expected symbol\"");
	}
	void _prompt() & {
		if( _out ) {
			for( int i = 0; i <= _depth; i++ ) {
				cout << '>';
			}
			cout << ' ' << flush;
		}
	}
	ClaimStatus get_claim_status( bool needsep = true ) {
		ClaimStatus cs;
		cs.name = _parser.gets_thm_name();
		while( _parser.skips("#") ) {
			if( _parser.skips("weak") ) {
				cs.weak = true;
			} else if( _parser.skips("force") ) {
				cs.force = true;
			} else if( _parser.skips("cong") ) {
				cs.cong = true;
			} else {
				throw Error("\"unknown #\"")(_parser.peek_token());
			}
		}
		if( _parser.skips("!") ) {
			cs.force = true;
		} else if( _parser.skips("?") ) {
			cs.weak = true;
		} else if( _parser.skips(":") ) {
		} else {
			if( needsep ) throw Error("\"expected ':'\"")(_parser.get());
			cs.followable = false;
		}
		return cs;
	}
	pair<ClaimStatus,Term> get_assm() {
		return {get_claim_status(),get_term()};
	}
	void add_claim( Thy& loc, ClaimStatus cs, Thm const& thm ) {
		if( cs.weak ) {
			add_forced(loc,thm);
		}
		if( cs.force ) {
			add_forced(loc,thm,true);
		}
		if( cs.cong ) {
			loc.add_thm(Rewriter::CONG,thm);
			_thy.rewriter().register_cong(thm);
		}
		if( cs.name ) {
			loc.add_thm(*cs.name,thm);
		}
	}
	void print_goal( Inference const& thesis, string pre = "goal " ) {
		if( _out ) {
			Term acc = thesis.thm();
			size_t i = 0;
			while( i < thesis.goal_count() ) {
				auto const& imp = acc.binary(IMP);
				i++;
				cout << pre << i << ": " << _thy.pretty(imp->first) << endl;
				acc = imp->second;
				pre = "\t";
			}
			if( i == 0 ) {
				cout << "no goal" << endl;
			}
		}
	}
	void for_variables( function<void( string const& v )> act ) {
		if( _parser.skips("for") ) {
			_cout << "for" << flush;
			while( auto const& sym = gets_sym() ) {
				_cout << ' ' << *sym << flush;
				act(*sym);
			}
			_parser.skip(",");
			_cout << ", ";
		}
	}
	/** Creates a nested theory, where outer one fixes free variables, and 
	 * inner theory collects assumptions.
	 */
	Inference get_statement() {
		auto assm_thy = _thy.branch("#proof","").thy();
		for_variables([&](auto const& v){ assm_thy.fix(v); });
		auto assms = vector<pair<ClaimStatus,CTerm>>();
		if( _parser.skips("if") ) {
			_cout << "if " << flush;
			for(;;) {
				if( _parser.skips("[") ) {
					_cout << "[ ";
					for(;;) {
						auto t = get_term();
						_cout << t;
						assms.push_back({{"",true},assm_thy.enclose(t)});
						if( !_parser.skips(",") ) break;
						_cout << ", ";
					}
					_parser.skip("]");
					_cout << " ] ";
				} else {
					auto [cs,t] = get_assm();
					assms.push_back({cs,assm_thy.enclose(t)});
					_cout << cs << _thy.pretty(t) << ", " << flush;
				}
				if( !_parser.skips(",") ) break;
			};
			_parser.skip("then");
			_cout << "then ";
			for( auto [cs,t] : assms ) {
				add_claim(assm_thy,cs,assm_thy.assume(t));
			}
		}
		Term conc = _parser.get_term(0);
		_parser.skip(";");
		CTerm goal = assm_thy.enclose(conc);
		_cout << _thy.pretty(goal) << endl;
		return Inference::claim_exact(assm_thy,goal);
	}
	void _auto_instantiate( Import& intp, string const& fix, bool change ) {
			intp.instantiate( change ? _thy.enclose(fix) : _thy.cterm(fix) );
	}
	void _auto_discharge( Thy& thy, string const& prefix, Import& intp, auto const& assume, bool change, Inference::Ctrl const& ctrl = Inference::DEFAULT_CTRL ) {
		string assm_name = prefix;
		if( prefix != "" ) {
			assm_name += '.';
		}
		assm_name += assume.second;
		auto const& assm = assume.first;
		if( auto opt = _thy.find_thm(assm_name,[&]( Term const& y ) { return assm == y; }) ) {
			intp.discharge(*opt);
		} else if( change ) {
			intp.discharge(thy.add_assm(assm_name,assm));
		} else {
			intp.discharge(prove(assm,_thy,ctrl));
		}
	}
	void _auto_retain( Thy& thy, string const& prefix, Import& intp, auto const& obtain ) {
		auto [sym,ex,spec,name] = obtain;
		if( auto csym = _thy.constant(sym) ) {
			Term const& stmt = spec.inst(*csym);
			auto const& thm = _thy.find_thm(name,[&]( AThm const& y ){ return stmt == y; });
			if( !thm ) throw Error("\"failed retain\"")(sym)(name)(stmt);
			intp.retain(*csym,*thm);
		} else {
			auto [sym_term,spec] = thy.obtain(sym,ex,name);
			intp.retain(sym_term,spec);
		}
	}
	void import( bool change ) {
		string prefix;
		string name = _parser.get_thm_name();
		if( _parser.skips(":") ) {
			swap(prefix,name);
			name = _parser.get();
		}
		auto im = _thy.find_thy(name,_read);
		if( !im ) throw Error("#theory_not_found")(name);
		auto& intp = _thy.add_import(prefix,*im);
		while( auto const& t = _parser.gets_term(1000) ) {
			for(;;) {
				if( auto const& fix = intp.fixing() ) {
					intp.instantiate(_thy.cterm(*t));
					break;
				} else if( auto const& assume = intp.assuming() ) {
					_auto_discharge(_thy,prefix,intp,*assume,change);
				} else if( auto const& obtain = intp.obtaining() ) {
					_auto_retain(_thy,prefix,intp,*obtain);
				} else {
					throw Error("\"unexpected instantiation\"")(*t);
				}
			}
		}
		if( _parser.skips(";") ) {
			_cout << (change ? "importing " : "interpreting ") << name << endl;
			_depth++;
			_prompt();
			_import_loop(prefix,intp,change);
			_depth--;
		} else {
			for(;;) {
				if( auto const& fix = intp.fixing() ) {
					_auto_instantiate(intp,*fix,change);
				} else if( auto const& assume = intp.assuming() ) {
					_auto_discharge(_thy,prefix,intp,*assume,change);
				} else if( auto const& obtain = intp.obtaining() ) {
					_auto_retain(_thy,prefix,intp,*obtain);
				} else {
					break;
				}
			}
		}
		_cout << (change ? "imported " : "interpreted ") << name << endl;
		_parser.skip(".");
	}
	size_t _print_import_goal( Import const& intp, size_t i, string const& pre ) {
		auto mod = intp.modification(i);
		if( auto const& fix = mod.ref<Import::Fix>() ) {
			cout << pre << "instantiate " << *fix;
			size_t n = 1;
			while( auto const& fix = intp.modification(n).ref<Import::Fix>() ) {
				cout << ", " << *fix;
				n++;
			}
			cout << endl;
			return n;
		} else if( auto const& assume = mod.ref<Import::Assume>() ) {
			cout << pre << "show " << assume->name << ": " << _thy.pretty(assume->assm) << endl;
			return 1;
		} else if( auto const& obtain = mod.ref<Import::Obtain>() ) {
			cout << pre << "retain " << obtain->spec_name << ": " << _thy.pretty(obtain->spec) << endl;
			return 1;
		} else {
			return 0;
		}
	}
	void _print_import_goals( Import const& intp ) {
		size_t i = 0;
		size_t n = _print_import_goal(intp,i,"goals: ");
		if( n == 0 ) {
			cout << "no instantiation goals" << endl;
			return;
		}
		for(;;) {
			i += n;
			n = _print_import_goal(intp,i,"\t");
			if( n == 0 ) return;
		}
	}
	void _import_loop( string const& prefix, Import& intp, bool change ) {
		auto org_thy = _thy;
		_thy = org_thy.scope("#import");// namespace
		_print_import_goals(intp);
		for(;;) try {
			_prompt();
			if( _term() || _thm() || _thms() || _ctxt() || _note() ) {
			} else if( _parser.skips("goals") ) {
				_print_import_goals(intp);
			} else if( _parser.skips("have") ) {
				_state();
			} else if( _parser.skips("interpret") ) {
				import(false);
			} else if( _parser.skips("show") ) {
				auto o = _state();
				if( o ) {
					auto const& [cs,thm] = *o;
					for(;;) {
						if( auto const& fix = intp.fixing() ) {
							_auto_instantiate(intp,*fix,change);
						} else if( auto const& obtain = intp.obtaining() ) {
							_auto_retain(org_thy,prefix,intp,*obtain);
							continue;
						} else if( auto assume = intp.assuming() ) {
							if( assume->first == thm ) break;
							_auto_discharge(org_thy,prefix,intp,*assume,change);
						} else {
							throw Error("\"unexpected show\"")(thm);
						}
					}
					intp.discharge(thm);
				}
			} else if( _parser.skips("instantiate") ) {
				vector<pair<string,Term>> ass;
				for(;;) {
					auto x = get_sym();// the symbol to be instantiated
					_parser.skip(":=");
					ass.emplace_back(x,_parser.get_term());
					if( !_parser.skips(",") ) break;
				}
				_parser.skip(".");
				for( auto [x,t] : ass ) {
					for(;;) {
						if( auto const& assume = intp.assuming() ) {
							_auto_discharge(org_thy,prefix,intp,*assume,change);
						} else if( auto const& obtain = intp.obtaining() ) {
							_auto_retain(org_thy,prefix,intp,*obtain);
						} else if( auto const& fix = intp.fixing() ) {
							if( *fix == x ) break;
							_auto_instantiate(intp,*fix,change);
						} else {
							throw Error("\"unexpected instantiate\"")(x);
						}
					}
					intp.instantiate( change ? org_thy.cterm(t) : org_thy.enclose(t) );
					_cout << "instantiating " << x << " := " << _thy.pretty(t) << endl;
				}
			} else if( _parser.skips("-") ) {
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& obtain = intp.obtaining() ) {
						_auto_retain(org_thy,prefix,intp,*obtain);
					} else {
						break;
					}
				}
				auto const& assume = intp.assuming();
				if( !assume ) throw Error("\"unexpected subgoal\"");
				auto [axiom,assm_name] = *assume;
				if( prefix != "" ) {
					assm_name = prefix + "." + assm_name;
				}
				if( _parser.skips(".") ) {
					_auto_discharge(org_thy,prefix,intp,*assume,false);
				} else if( change && _parser.skips("assume") ) {
					_parser.skip(".");
					Thm thm = org_thy.add_assm(assm_name,axiom);
					intp.discharge(thm);
					_cout << "assumed " << assm_name << ": " << _thy.pretty(thm) << endl;
				} else {
					if( auto thm = _subgoal(axiom) ) {
						intp.discharge(*thm);
					}
				}
			} else if( _parser.skips("obtain") ) {
				_obtain(org_thy);
			} else if( _parser.skips("define") ) {
				_define(org_thy);
			} else if( _parser.skips("retain") ) {
				_retain(prefix,intp,change,org_thy);
			} else if( _parser.skips("oops") ) {
				_cout << "oops" << endl;
				_prompt();
				break;
			} else if( _parser.skips("") ) {
				cerr << _parser.location() << ": Unexpected EOF" << endl;
				exit(0);
			} else {
				Inference::Ctrl ctrl;
				if( _parser.skips("by") ) {
					get_ctrl(ctrl);
				}
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& assume = intp.assuming() ) {
						_auto_discharge(org_thy,prefix,intp,*assume,change,ctrl);
					} else if( auto const& obtain = intp.obtaining() ) {
						_auto_retain(org_thy,prefix,intp,*obtain);
					} else {
						break;
					}
				}
				break;
			}
			if( _out ) {
				_print_import_goal(intp,0,"next ");
			}
		} catch( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _thy.pretty(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
		_thy = org_thy;
	}
	void _retain( string const& prefix, Import& intp, bool change, Thy& org_thy ) {
		auto sym = get_sym();// the symbol to be instantiated
		Thy thesis_loc = _thy.branch().thy();
		auto term = org_thy.cterm( _parser.skips(":=") ? _parser.get_term() : sym );
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change);
			} else if( auto const& assume = intp.assuming() ) {
				_auto_discharge(org_thy,prefix,intp,*assume,change);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto const& [osym,ex,spec,spec_name] = *obtain;
				if( osym == sym ) {
					CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
						return _thy.constant(x);
					}));
					CTerm t = ex.capp()->second;
					// var'. (∀sym. props... ⟹ var') ⟹ var'
					t = thesis_loc.weaken(t).inst(var);
					// (∀sym. props... ⟹ var) ⟹ var
					t = t.cbinary(IMP)->first;
					// ∀sym. props... ⟹ var
					t = t.capp()->second.inst(thesis_loc.weaken(term));
					// props[sym:=term]... ⟹ var
					auto const& rule = Intro::rule(thesis_loc.add_assm("?thesis",t));
					// assume this and prove var, i.e., prove props[sym:=term]...
					auto thesis = Inference::claim_exact(thesis_loc,var);// var ⟹ var
					thesis.apply(rule);// prop[sym:=term]... ⟹ var
					if( _parser.skips(";") ) {
						print_goal(thesis);
						auto prf = Prover(*this,thesis_loc).deepen().proof_loop(thesis);
						_parser.skips(".");
						if( prf ) {
							auto const& spec = prf->intro();
							// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
							intp.retain(term,spec);
						}
					} else {
						_parser.skips(".");
						intp.retain(term,thesis.blast_all().intro());
					}
					break;
				}
				_auto_retain(org_thy,prefix,intp,*obtain);
			} else {
				throw Error("\"unexpected retain\"")(sym);
			}
		}
	}
	void get_rules( set<Intro>& rules ) {
		while( auto thm = gets_thm() ) {
			if( _parser.skips("!") ) {
				size_t n = _parser.get_nat();
				rules.emplace(Intro::imp(*thm,n));
			} else if( _parser.skips("=") ) {
				rules.emplace(Intro::axiom(*thm));
			} else {
				rules.emplace(Intro::rule(*thm));
			}
		}
	}
	void get_ctrl( Inference::Ctrl& ctrl ) {
		get_rules(ctrl.intros);
		while( _parser.skips("#") ) {
			if( _parser.skips("elim") ) {
				while( auto elim = gets_thm() ) {
					ctrl.elims.emplace(Elim::rule(*elim));
				}
			} else if( bool dir = false; _parser.skips("unfold") || (dir = true, _parser.skips("fold") ) ) {
				auto [rrules,rctrl] = _get_rewrite(_thy.self(),dir);
				rctrl.min = 0;// returns false when not applicable
				ctrl.rewrite = {{rrules,rctrl}};
			} else if( _parser.skips("force") ) {
				ctrl.force_assms = true;
			} else {
				throw Error("\"unexpected\"")(_parser.peek_token());
			}
		}
	}

	bool _ctxt() {
		if( _parser.skips("ctxt") ) {
			if( _parser.skips(".") ) {
				_cout << _thy << endl;
			} else {
				string name = _parser.get();
				_parser.skip(".");
				auto im = _thy.find_thy(name,_read);
				if( !im ) throw Error("\"theory not found\"");
				_cout << im->thy() << endl;
			}
			return true;
		}
		return false;
	}
	bool _thm() {
		if( _parser.skips("thm") ) {
			string pref = "thm ";
			do {
				Thm thm = get_thm();
				_cout << pref << _thy.pretty(thm) << endl;
				pref = "\t";
			} while( !_parser.skips(".") );
			return true;
		}
		return false;
	}
	bool _thms() {
		if( _parser.skips("thms") ) {
			bool shp = _parser.skips("#");
			string name = _parser.get_thm_name();
			string ref = shp ? "#"+name : name;
			cout << "thms " << ref << ":\n" << _thy.print_thms(ref);
			_parser.skip(".");
			return true;
		}
		return false;
	}
	bool _term() {
		if( _parser.skips("term") ) {
			Term term = get_term();
			_parser.skip(".");
			cout << "term " << _thy.pretty(term) << endl;
			return true;
		}
		return false;
	}
	bool _note() {
		if( _parser.skips("note") ) {
			auto cs = get_claim_status();
			auto thm = get_thm();
			add_claim(_thy,cs,thm);
			_cout << "note " << cs << _thy.pretty(thm) << endl;
			while( auto o = gets_thm() ) {
				add_claim(_thy,cs,*o);
				_cout << "\t" << cs << _thy.pretty(*o) << endl;
			}
			_parser.skip(".");
			return true;
		}
		return false;
	}
	Opt<pair<ClaimStatus,Thm>> _state() {
		auto cs = get_claim_status();
		_cout << "showing " << cs << flush;
		auto thesis = get_statement();
		auto prev_thy = _thy;
		_thy = thesis.thy();
		_depth++;
		_prompt();
		auto o = proof_loop(thesis);
		_thy = prev_thy;
		_depth--;
		if( o ) {
			auto thm = o->intro();
			add_claim(_thy,cs,thm);
			_parser.skip(".");
			return {{cs,thm}};
		}
		return {};
	}
	void _define( Thy& thy ) {
		Opt<string> name_op;
		if( _parser.skips("[") ) {
			name_op = _parser.get();
			_parser.skip("]");
		}
		Term l = get_term();
		_parser.skip(":=");
		Term r = get_term();
		_parser.skip(".");
		auto [f,spec] = thy.define(l,r,name_op);
		Thm def = spec << _thy.thm("imp.refl");
		string name = (name_op ? *name_op : f) + "_def";
		_thy.add_thm(name,def);
		_cout << "defined " << name << ": " << _thy.pretty(l) << " := " << _thy.pretty(r) << endl;
	}
	Opt<Thm> _subgoal( CTerm const& goal ) {
		auto subintp = _thy.branch();
		auto& subloc = subintp.thy();
		CTerm subgoal = subloc.weaken(goal);
		bool needsep = false;
		if( _parser.skips("for") ) {// instantiate variables as long as names are given
			needsep = true;
			if( _out ) {
				cout << "for";
				subgoal = strip_all(subgoal,subloc.self(),[&](string_view const& v){
					auto o = gets_sym();
					if( o ) {
						cout << ' ' << *o;
					}
					return o;
				});
				_parser.skips(",");
				cout << ", ";
			} else {
				subgoal = strip_all(subgoal,subintp,[&](string_view const& v){ return gets_sym(); });
				_parser.skips(",");
			}
		}
		if( _parser.skips("if") ) {
			needsep = true;
			_cout << "if ";
			auto eat_assm = [&]( Opt<Term> const& t ){
				auto imp = subgoal.cbinary(IMP);
				if( !imp ) throw Error("\"unexpected assumption\"")(subgoal);
				auto assm = imp->first;
				if( t && assm != *t ) throw Error("\"assumption mismatch\"")(assm)(*t);
				subgoal = imp->second;
				return subloc.assume(assm);
			};
			for(;;) {
				if( _parser.skips("[") ) {
					_cout << "[ ";
					for(;;) {
						auto assm = eat_assm(get_term());
						add_forced(subloc,assm,true);
						_cout << _thy.pretty(assm);
						if( !_parser.skips(",") ) break;
						_cout << ", ";
					}
					_parser.skip("]");
					_cout << " ] ";
				} else {
					auto cs = get_claim_status(false);
					auto assm = eat_assm( cs.followable ? gets_term() : Opt<Term>{} );
					add_claim(subloc,cs,assm);
					_cout << cs << _thy.pretty(assm) << ", " << flush;
				}
				if( !_parser.skips(",") ) break;
			};
		}
		if( _parser.skips("then") ) {
			if( _parser.get_term() != subgoal ) {
				throw Error("\"conclusion mismatch\"")(subgoal);
			}
		}
		auto prover = Prover(*this,subloc);
		prover._depth++;
		if( _parser.skips(".") ) {
			return {prove(subgoal,subloc).intro()};
		}
		if( needsep ) {
			_parser.skip(";");
			_cout << "show " << _thy.pretty(subgoal) << endl;
			prover._prompt();
		}
		auto thesis = Inference::claim_exact(subloc,subgoal);
		auto thm = prover.proof_loop(thesis);
		if( thm ) {
			_parser.skip(".");
			return thm->intro();
		}
		return {};
	}
	bool _thy_decl() {
		if( _parser.skips("theory") ) {
			string name = _parser.get(Parser::Word);
			auto loc = _thy.branch(name,"").thy();
			while( auto sym = gets_sym() ) {
				loc.fix(*sym);
			}
			if( _parser.skips(":") ) {
				_cout << "creating theory " << name << endl;
				Prover(*this,loc).deepen().loop();
				_cout << "end theory " << name << endl;
			}
		} else if( _parser.skips("namespace") ) {
			auto name = _parser.get(Parser::Word);
			_parser.skip("begin");
			_cout << "creating namespace " << name << endl;
			auto im = _thy.branch();
			Prover(*this,im.thy()).deepen().loop();
			_thy.add_import(name,im);
			_cout << "end namespace " << name << endl;
		} else if( _parser.skips("context") ) {
			string name = _parser.get();
			_parser.skip("begin");
			auto im = _thy.find_thy(name,_read);
			_cout << "in context " << name << endl;
			Prover(*this,im->thy()).deepen().loop();
			_cout << "left " << name << endl;
		} else if ( _parser.skips("lemma") ||
			_parser.skips("theorem") ||
			_parser.skips("proposition")
		) {
			auto o = _state();
			if( _out && o ) {
				auto const& [cs,thm] = *o;
				cout << "proved " << cs << _thy.pretty(thm) << endl;
			}
		} else {
			return false;
		}
		return true;
	}
	bool _stat() {
		return _ctxt() || _thm() || _thms() || _term() || _note();
	}
	bool _shared_decl() {
		if( _parser.skips("obtain") ) {
			_obtain(_thy);
		} else if( _parser.skips("define") ) {
			_define(_thy);
		} else if( _parser.skips("interpret") ) {
			import(false);
		} else {
			return false;
		}
		return true;
	}
	Opt<Thm> proof_loop( Inference& thesis ) {
		for(;;) try {
			if( _stat() || _shared_decl() ) {
			} else if( _parser.skips("goal") ) {
				_parser.skip(".");
				print_goal(thesis);
			} else if( _parser.skips("have") ) {
				_state();
				print_goal(thesis);
			} else if( _parser.skips("show") ) {
				auto o = _state();
				if( o ) {
					while( thesis.goal() != o->second ) {
						thesis.blast();
					}
					thesis.discharge(o->second);
				}
				print_goal(thesis);
			} else if( _parser.skips("apply") ) {
				int min, max;
				bool safe, wide;
				if( _parser.skips("+") ) {
					min = 1; max = 255; safe = false; wide = true;
				} else {
					min = max = 1; safe = true; wide = false;
				}
				auto rules = set<Intro>();
				get_rules(rules);
				thesis.apply(rules,min,max,safe,wide);
				if( _parser.skips(";") ) {
					print_goal(thesis,"applied goals:\n\t");
				} else {
					return thesis.blast_all();
				}
			} else if( bool dir = false; _parser.skips("unfold") || ( dir = true, _parser.skips("fold") ) ) {
				auto [rules,ctrl] = _get_rewrite(_thy.self(),dir);
				_thy.rewriter().apply(rules,thesis,ctrl);
				if( _parser.skips(";") ) {
					print_goal( thesis, dir ? "folded goal " : "unfolded goal " );
				} else {
					return thesis.blast_all();
				}
			} else if( _parser.skips("-") ) {
				auto goal = thesis.has_goal();
				if( !goal ) {
					throw Error("\"unexpected subgoal\"");
				}
				auto thm = _subgoal(*goal);
				if( thm ) {
					thesis.discharge(*thm);
					print_goal(thesis,"next goal ");
				} else {
					print_goal(thesis);
				}
			} else if( _parser.skips("by") ) {
				Inference::Ctrl ctrl;
				get_ctrl(ctrl);
				return thesis.blast_all(ctrl);
			} else if( _parser.skips("oops") ) {
				_cout << "oops" << endl;
				return {};
			} else if( _parser.skips("") ) {
				cerr << _parser.location() << ": Unexpected EOF" << endl;
				exit(0);
			} else {
				auto thm = thesis.blast_all();
				return thm;
			}
			_prompt();
		} catch ( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _thy.pretty(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
	}
	void loop() {
		for(;;) try {
			if( _stat() || _thy_decl() || _shared_decl() ) {
			} else if( _parser.skips("setup") ) {
				if( _parser.skips("rewrite") ) {
					bool def = _parser.skips("!") || _thy.rewriter().empty();
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					_cout << "registering rewriter:\n\timp: " << _thy.pretty(imp) <<
						"\n\trev: " <<  _thy.pretty(revimp) <<
						"\n\trefl: " << _thy.pretty(refl) <<
						"\n\ttrans: " << _thy.pretty(trans);
					_thy.rewriter().register_refl(refl,def).
						register_imp(imp,true).
						register_imp(revimp,false).
						register_trans(trans);
					_thy.find_thm( Rewriter::CONG, [&](AThm const& thm ){
						_thy.rewriter().register_cong(thm);
						_cout << "\n\tcong: " << _thy.pretty(thm);
						return false;
					} );
					_cout << endl;
				} else if( _parser.skips("trans") ) {
					_cout << "registering transitivity: ";
					while( auto const& thm = gets_thm() ) {
						_thy.rewriter().register_trans(*thm);
						_cout << _thy.pretty(*thm);
					}
					_cout << endl;
				} else if( _parser.skips("dual") ) {
					_cout << "registering dual: ";
					while( auto const& thm = gets_thm() ) {
						_thy.rewriter().register_dual(*thm);
						_cout << _thy.pretty(*thm);
					};
					_cout << endl;
				} else if( _parser.skips("define") ) {
					Thm const& beta = get_thm();
					_cout << " beta: " << _thy.pretty(beta) << endl;
					_thy.setup_definer(beta);
				} else if( _parser.skips("set_comprehension") ) {
					Term const& collect = _parser.get_term(1000);
					Term const& lambda = _parser.get_term(1000);
					Term const& empty = _parser.get_term(1000);
					Term const& singleton = _parser.get_term(1000);
					Term const& un = _parser.get_term(1000);
					auto handler = [=,*this](Parser& parser) {
						auto const& inner = parser.gets_term(-1);
						if( !inner ) {
							parser.skip("}");
							return empty;
						}
						if( inner->bind() ) {
							parser.skip("}");
							return collect(lambda(*inner));
						}
						Term ret = singleton(*inner);
						while( parser.skips(",") ) {
							auto const inner2 = parser.gets_term(0);
							ret = un(ret)(singleton(*inner2));
						}
						parser.skip("}");
						return ret;
					};
					_thy.syntax().opener("{",-1000,handler);
					_thy.syntax().closer("}");
					_cout << "set up set comprehension" << endl;
				} else if( _parser.skips("print") ) {
					if( _parser.skips("ctxt_id") ) {
						_thy.syntax().print_ctxt(true);
					}
				}
				_parser.skip(".");
			} else if( _parser.skips("symbol") ) {
				bool solo = _parser.skips("solo");
				_cout << "registering symbols";
				while( !_parser.skips(".") ) {
					string const& sym = _parser.get();
					int ch = int_of_chars(sym.data());
					if( solo ) {
						_thy.syntax().register_single_op(ch);
					} else {
						_thy.syntax().register_multi_op(ch);
					}
					_cout << ' ' << sym;
				}
				_cout << endl;
			} else if( _parser.skips("prefix") ) {
				string sym = _parser.get();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_make_own_parser();
				_thy.syntax().prefix(sym,level,rlevel);
				_cout << "new prefix operator " << sym << endl;
				_parser.skip(".");
			} else if( _parser.skips("infix") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_make_own_parser();
				_thy.syntax().infix(sym,level,llevel,rlevel);
				_cout << "new infix operator " << sym << endl;
				_parser.skip(".");
			} else if( _parser.skips("binder") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				_make_own_parser();
				_thy.syntax().binder(sym,llevel,rlevel);
				_cout << "new binder " << sym << endl;
				_parser.skip(".");
			} else if( _parser.skips("binder_middle") ) {
				string prefix = _parser.get();
				string mid = _parser.get();
				string sym = _parser.get();
				_make_own_parser();
				_thy.syntax().binder_mid(prefix,mid,sym);
				_cout << "new binder middle " << prefix << " x " << mid << " y. z := " << sym << " y (x. z)" << endl;
				_parser.skip(".");
			} else if( _parser.skips("end") || _parser.skips("") ) {
				return;
			} else if( !_final ) {
				if( _parser.skips("fix") ) {
					_cout << "fixing";
					for(;;) {
						if ( auto sym = gets_sym() ) {
							_thy.fix(*sym);
							_cout << ' ' << *sym << flush;
						} else {
							break;
						}
					}
					_cout << '.' << endl;
					_parser.skip(".");
				} else if( _parser.skips("assume") ) {
					auto cs = get_claim_status();
					Ctxt var_loc = _thy.Ctxt::branch().ctxt();
					if( _parser.skips("for") ) {
						while( auto const& sym = gets_sym() ) {
							var_loc.fix(*sym);
						}
						_parser.skip(",");
					}
					for_variables([&]( auto& var ){ var_loc.fix(var); });
					CTerm assm = var_loc.enclose(get_term()).lift(_thy.cterm(ALL));
					Thm thm = cs.name ? _thy.add_assm(*cs.name,assm) : _thy.assume(assm);
					add_claim(_thy,cs,thm);
					_cout << "assumed " << cs << _thy.pretty(assm) << ". " << endl;
					_parser.skip(".");
				} else if( _parser.skips("import") ) {
					import(true);
				} else if( _parser.skips("begin") ) {
					_final = true;
					_cout << "finalized" << endl;
				} else {
					throw Error("unexpected")(_parser.get());
				}
			} else {
				throw Error(Term("unexpected")(_parser.get()));
			}
			_prompt();
		} catch ( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _thy.pretty(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
	}
	void _obtain( Thy& org_thy ) {
		string sym = get_sym();
		_parser.skip("where");
		_cout << "obtaining " << sym << " where" << endl;
		vector<CTerm> props;
		vector<pair<ClaimStatus,Thm>> prop_thms;
		Thy thesis_thy = org_thy.branch().thy();
		CTerm var = thesis_thy.fix("?thesis");
		Thy goal_thy = thesis_thy.branch().thy();
		goal_thy.fix(sym);
		auto props_thy = org_thy.branch().thy();
		props_thy.fix(sym);
		for(;;) {
			auto [cs,t] = get_assm();
			Thm thm = props_thy.assume(props_thy.branch().ctxt().enclose(t).intro());
			add_claim(props_thy,cs,thm);
			prop_thms.emplace_back(cs,thm);
			props.push_back(goal_thy.branch().ctxt().enclose(t).intro());
			_cout << '\t' << cs << _thy.pretty(thm) << endl;
			if( !_parser.skips(",") ) break;
		}
		_parser.skip(";");
		CTerm goal = goal_thy.weaken(var);
		for( auto& prop : ranges::reverse_view(props) ) {
			goal = prop >>= goal;
		}
		goal = goal.lift(thesis_thy.cterm(ALL)) >>= var;
		goal = goal.lift(org_thy.cterm(ALL));
		_prompt();
		_cout << "prove " << _thy.pretty(goal) << endl;
		auto thesis = Inference::claim_exact(org_thy,goal);
		auto const& thm = Prover(*this,org_thy).deepen().proof_loop(thesis);
		if( thm ) {
			auto [sym_term,deriver] = org_thy.obtain(sym,*thm,make_spec_name(string(sym)));
			// deriver: ∀thesis. (p ⟹ ... ⟹ thesis) ⟹ thesis
			for( auto const& [cs,prop_thm] : prop_thms ) {
				auto const& arg = prop_thm.intro();// props... ⟹ prop_i
				Thm prop = deriver << arg;// prop_i
				add_claim(_thy,cs,prop);
			}
			_cout << "obtained " << sym << endl;
			_parser.skip(".");
		}
	}
	void move_to_thy( Thy const& thy ) {
		_thy = thy;
	}
private:
	void _make_own_parser() {
/*		if( !_own_parser ) {
			_parser.fork();
			_own_parser = true;
		}
*/	}
};

void _read( Thy& thy, Parser& parser ) {
	Prover(thy,parser,true).loop();
}
void run( istream& is, string_view const& name, bool exit_on_error, bool out, bool load_out ) {
	auto root = Thy("Root","Root");// the empty root theory, linked to the "Root" directory
	init_syntax(root.syntax());
	Thy thy = root.branch(name,"").thy();
	auto lexer = Lexer(is,name,thy.syntax());
	auto parser = Parser(lexer,thy.syntax());
	auto prover = Prover(thy,parser,exit_on_error);
	prover.set_out(out,load_out);
	try {
		prover.loop();
	} catch( Error const& e ) {
		cerr << lexer.location() << ": ERROR: " << e << endl;
		exit(-1);
	}
}

int main(int argc, char* argv[]) {
	bool exit_on_error = false;
	if( argc == 1 ) {
		run(cin,"#stdin",false,true,false);
	} else {
		string name = argv[1];
		auto fin = fstream(name);
		run(fin,name,true,true,true);
	}
	cout << "bye!" << endl;
	return 0;
}

