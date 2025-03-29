#include<fstream>
#include<filesystem>
#include<ranges>
#include"theory.hpp"
#include"parser.hpp"
#include"definer.hpp"

#define _cout if(_out) cout

using namespace std;

struct ClaimStatus {
	Opt<string> name;
	bool weak = false, force = false, cong = false;
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

Ref<Syntax> make_syntax() {
	auto ret = Ref<Syntax>::make();
	ret->register_multi_op(int_of_chars("∀"));
	ret->register_multi_op(int_of_chars("⟹"));
	ret->register_single_op(',');
	ret->register_single_op(';');
	ret->register_multi_op(':');
	ret->register_multi_op('=');
	ret->register_multi_op('!');
	ret->register_multi_op('?');
	ret->register_multi_op('*');
	ret->register_multi_op('+');
	ret->register_multi_op('-');
	ret->register_multi_op('#');
	ret->opener("(",-1000,[&]( Parser& parser ){
		Opt<Term> t = parser.gets_term(-1000);
		parser.skip(")");
		return *t;
	});
	ret->closer(")");
	ret->closer("}");
	ret->closer("]");
	ret->infix(",",-2,-2,-3);
	ret->infix(";",-3,-3,-4);
	ret->infix(":=",-1,-1,-2);
	ret->prefix("if",-1,-2);
	ret->infix("then",-2,-1,-2);
	ret->infix("else",-2,-2,-1);
	return ret;
}

static Error const ProofMismatch = Error("#proof-mismatch");

class Prover {
	unsigned int _depth;
	Thy _thy;
	bool _own_parser;
	Ref<Syntax> _syntax;
	Parser _parser;
	bool _exit_on_error;
	bool _final = false;
	bool _out = true;
	Prover( Prover& parent, Thy const& loc ) :
		_depth(parent._depth),
		_thy(loc),
		_syntax(parent._syntax),
		_parser(parent._parser.get_lexer(),*parent._syntax),
		_own_parser(false),
		_exit_on_error(parent._exit_on_error),
		_out(parent._out) {
	}
public:
	struct Error : ::Error {
		static inline Term const RT = Term("#prover_error");
		Error( Term const& msg ) : ::Error(RT(msg)) {
		}
	};
	Prover( Lexer& lexer, Ref<Syntax> syntax, bool exit_on_error ) :
		_depth(0),
		_thy("Root","Root/"),
		_syntax(syntax),
		_parser(lexer,*_syntax),
		_own_parser(true),
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
		_thy = _thy.branch(name,dirname);
		_final = false;
	}
	void set_exit_on_error( bool b ) {
		_exit_on_error = b;
	}
	void set_out( bool b ) {
		_out = b;
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
		if( auto thm = gets_thm() ) {
			return *thm;
		}
		throw Parser::Error("expects a theorem");
	}
	pair<Rewriter::Rules,Rewriter::Ctrl> _get_rewrite( Thy& loc, bool rev = false ) {
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
			_thy.rewriter().add_rule( loc, rules, *arg, _parser.skips("-") ? !rev : rev );
			n++;
		}
		if( ctrl.max < n ) {
			ctrl.max = n;
		}
		return ret;
	}

	Opt<Thm> _gets_thm(Thy loc) {
		auto const& opt = _parser.gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = loc.thm(*opt);
		for(;;) {
			if( _parser.skips("(") ) {
				do {
					ret = ret.instantiate(loc.enclose(_parser.get_term(-1)));
				} while( _parser.skips(",") );
				_parser.skip(")");
			} else if( _parser.skips("[") ) {
				if( _parser.skips("OF") ) {
					for(;;) {
						if( _parser.skips("!") ) {
							auto opt = blasts(ret,loc);
							if( !opt ) throw Error("\"blast failed\"")(ret);
							ret = *opt;
						} else if( auto const& arg = _gets_thm(loc) ) {
							ret = discharge(ret,*arg);
						} else {
							break;
						}
					}
				} else if( bool dir = false; _parser.skips("unfolded") || (dir = true, _parser.skips("folded")) ) {
					auto [rules,ctrl] = _get_rewrite(loc,dir);
					ret = _thy.rewriter().rewrite(rules,loc,ret,ctrl);
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
	ClaimStatus get_claim_status() {
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
		} else {
			_parser.skip(":");
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
	Thy find_thy( Thy const& thy, string_view path ) {
		if( auto o = thy.find_thy(path) ) {
			return *o;
		}
		auto ret = thy;
		while( path[0] == '.' ) {
			path = path.substr(1);
			auto p = ret.parent();
			if( !p ) throw Error("no more ancestor");
			ret = *p;
		}
		for(;;) {
			auto i = path.find('.');
			if( i == string::npos ) break;
			auto cur = path.substr(0,i);
			if( auto o = ret.find_thy(cur,false) ) {
				ret = *o;
			} else {
				ret = load_thy(ret,cur);
			}
			path = path.substr(i+1);
		}
		if( auto o = ret.find_thy(path,false) ) {
			return *o;
		} else {
			return load_thy(ret,path);
		}
	}
	void print_goal( Inference const& thesis, string pre = "goal " ) {
		if( _out ) {
			Term acc = thesis.thm();
			size_t i = 0;
			while( i < thesis.goal_count() ) {
				auto const& imp = acc.binary(IMP);
				i++;
				cout << pre << i << ": " << _syntax->pretty_term(imp->first) << endl;
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
		auto var_thy = _thy.branch();
		auto assm_thy = var_thy.branch("#proof","");
		for_variables([&](auto const& v){ var_thy.fix(v); });
		if( _parser.skips("if") ) {
			_cout << "if " << flush;
			auto add_assm = [&]( Term const& t ) {
				return assm_thy.assume(var_thy.enclose(t).weaken(assm_thy));
			};
			for(;;) {
				if( _parser.skips("[") ) {
					_cout << "[ ";
					for(;;) {
						auto t = get_term();
						_cout << t;
						add_forced(assm_thy,add_assm(t),true);
						if( !_parser.skips(",") ) break;
						_cout << ", ";
					}
					_parser.skip("]");
					_cout << " ] ";
				} else {
					auto [cs,t] = get_assm();
					add_claim(assm_thy,cs,add_assm(t));
					_cout << cs << _syntax->pretty_term(t) << ", " << flush;
				}
				if( !_parser.skips(",") ) break;
			};
			_parser.skip("then");
			_cout << "then ";
		}
		Term conc = _parser.get_term(0);
		_parser.skip(";");
		CTerm goal = var_thy.enclose(conc).weaken(assm_thy);
		_cout << _syntax->pretty_cterm(goal) << endl;
		return Inference::claim_exact(assm_thy,goal);
	}
	void import( bool mod ) {
		string prefix;
		string name = _parser.get_thm_name();
		if( _parser.skips(":") ) {
			prefix = name;
			name = _parser.get();
		}
		auto loc = find_thy(_thy,name);
		auto& intp = _thy.import(prefix,loc);
		while( auto const& t = _parser.gets_term(1000) ) {
			while( intp.discharges(mod) || intp.retains() );
			auto const& fix = intp.fixing();
			if( !fix ) {
				throw Error("\"too many instantiation\"")(*t);
			}
			auto v = *fix;
			if( *t == "_" ) {
				auto t = _thy.constant(v);
				if( t ) intp.instantiate(*t);
				else if( mod ) intp.instantiate(_thy.fix(v));
				else throw Error("\"instantiation must be specified\"")(v);
			} else {
				intp.instantiate( mod ? _thy.cterm(*t) : _thy.enclose(*t) );
			}
		}
		if( _parser.skips(";") ) {
			_cout << (mod ? "importing " : "interpreting ") << name << endl;
			_depth++;
			_prompt();
			_import_loop(intp,mod);
			_depth--;
		} else {
			_parser.skip(".");
			while( intp.instantiates(mod) || intp.discharges(mod) || intp.retains() );
		}
		if( !intp.ready() ) throw Error("\"failed to interpret\"");
		_cout << (mod ? "imported " : "interpreted ") << name << endl;
	}
	void _import_loop( Import& intp, bool mod ) {
		auto org_thy = _thy;
		_thy = Thy(org_thy,org_thy,"#import","");// namescope
		for(;;) try {
			if( _out ) {
				if( auto x = intp.fixing() ) {
					cout << "fix " << *x << endl;
				} else if( auto x = intp.assuming() ) {
					auto [name,axiom] = *x;
					cout << "show " << name << ": " << _syntax->pretty_cterm(axiom) << endl;
				} else if( auto x = intp.obtaining() ) {
					cout << "obtain " << x->sym << " in " << _syntax->pretty_cterm(x->spec) << endl;
				} else {
					cout << "completed" << endl;
				}
				_prompt();
			}
			if( _term() || _thm() || _thms() || _ctxt() || _note() ) {
			} else if( _parser.skips("have") ) {
				_state();
			} else if( _parser.skips("interpret") ) {
				import(false);
			} else if( _parser.skips("show") ) {
				auto o = _state();
				if( o ) {
					auto const& [cs,thm] = *o;
					for(;;) {
						if( intp.instantiates(mod) || intp.retains() ) continue;
						auto a = intp.assuming();
						if( !a ) throw Error("\"unexpected show\"")(thm);
						if( a->second != thm ) {
							intp.discharge();
							continue;
						}
						intp.discharge(thm);
						break;
					}
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
						if( intp.discharges(mod) || intp.retains() ) continue;
						auto y = intp.fixing();
						if( !y ) throw Error("\"unexpected instantiate\"")(x);
						if( *y == x ) break;
						intp.instantiates(mod);
					}
					intp.instantiate( mod ? org_thy.cterm(t) : org_thy.enclose(t) );
					_cout << "instantiating " << x << " := " << _syntax->pretty_term(t) << endl;
				}
			} else if( _parser.skips("-") ) {
				while( intp.instantiates(mod) || intp.retains() );
				auto a = intp.assuming();
				if( !a ) throw Error("\"unexpected discharge\"");
				auto [name,axiom] = *a;
				if( _parser.skips("know") ) {
					_parser.skip(".");
					intp.discharge();
				} else if( mod && _parser.skips("assume") ) {
					_parser.skip(".");
					Thm thm = org_thy.add_assm(name,axiom);
					intp.discharge(thm);
					_cout << "assumed " << _syntax->pretty_thm(thm) << endl;
				} else {
					if( auto thm = _subgoal(axiom) ) {
						intp.discharge(*thm);
					}
				}
			} else if( _parser.skips("obtain") ) {
				_obtain();
			} else if( _parser.skips("retain") ) {
				auto sym = get_sym();// the symbol to be instantiated
				_parser.skip(":=");
				Thy thesis_loc = _thy.branch();
				auto term = thesis_loc.cterm(_parser.get_term());
				_parser.skip(";");
				for(;;) {
					if( intp.discharges(mod) || intp.instantiates(mod) ) continue;
					auto x = intp.obtaining();
					if( !x ) throw Error("\"unexpected retain\"")(sym);
					if( x->sym != sym ) {
						assert(intp.retains());
						continue;
					}
					CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
						return _thy.constant(x);
					}));
					CTerm t = x->ex.capp()->second;
		// var'. (∀sym. props... ⟹ var') ⟹ var'
					t = t.weaken(thesis_loc).inst(var);
		// (∀sym. props... ⟹ var) ⟹ var
					t = t.cbinary(IMP)->first;
		// ∀sym. props... ⟹ var
					t = t.capp()->second.inst(term);
		// props[sym:=term]... ⟹ var
					auto const& rule = Intro::rule(thesis_loc.add_assm("?thesis",t));
		// assume this and prove var, i.e., prove props[sym:=term]...
					auto thesis = Inference::claim_exact(thesis_loc,var);// var ⟹ var
					thesis.apply(rule);// prop[sym:=term]... ⟹ var
					auto prf = Prover(*this,thesis_loc).deepen().proof_loop(thesis);
					if( prf ) {
						auto const& spec = prf->intro();
		// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
						intp.retain(org_thy.cterm(term),spec);
					}
					break;
				}
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
				_parser.skip(".");
				for(;;) {
					if( intp.instantiates(mod) || intp.retains() ) continue;
					if( auto a = intp.assuming() ) {
						auto& [name,assm] = *a;
						if( _thy.find_thm(name,[&](auto thm){
							if( thm == assm ) {
								intp.discharge(thm);
								return true;
							}
							return false;
						},true,true) ) {
							continue;
						}
						intp.discharge(prove(assm,_thy,ctrl));
						continue;
					}
					break;
				}
				break;
			}
		} catch( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _syntax->pretty_term(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
		_thy = org_thy;
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
				auto [rrules,rctrl] = _get_rewrite(_thy,dir);
				rctrl.min = 0;// returns false when not applicable
				ctrl.extra = [rrules,rctrl,this](Inference& thesis){
					return _thy.rewriter().apply(rrules,thesis,rctrl);
				};
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
				_cout << _thy.pretty(*_syntax) << endl;
			} else {
				string name = _parser.get();
				_parser.skip(".");
				auto loc = find_thy(_thy,name);
				_cout << loc.pretty(*_syntax) << endl;
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
				_cout << pref << _syntax->pretty_thm(thm) << ';' << endl;
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
			cout << "term " << _syntax->pretty_term(term) << endl;
			return true;
		}
		return false;
	}
	bool _note() {
		if( _parser.skips("note") ) {
			auto cs = get_claim_status();
			auto thm = get_thm();
			add_claim(_thy,cs,thm);
			_cout << "note " << cs << _syntax->pretty_thm(thm) << endl;
			while( auto o = gets_thm() ) {
				add_claim(_thy,cs,*o);
				_cout << "\t" << cs << _syntax->pretty_thm(*o) << endl;
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
			auto thm = o->intro().intro();
			add_claim(_thy,cs,thm);
			return {{cs,thm}};
		}
		return {};
	}
	void _define() {
		Opt<string> name_op;
		if( _parser.skips("[") ) {
			name_op = _parser.get();
			_parser.skip("]");
		}
		Term l = get_term();
		_parser.skip(":=");
		Term r = get_term();
		_parser.skip(".");
		auto [f,spec] = _thy.define(l,r,name_op);
		Thm def = spec << _thy.thm("imp.refl");
		string name = name_op ? *name_op : f + "_def";
		_thy.add_thm(name,def);
		_cout << "defined " << name << ": " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
	}
	Opt<Thm> _subgoal( CTerm const& goal ) {
		auto subloc = _thy.branch();
		CTerm subgoal = goal.weaken(subloc);
		bool needsep = false;
		if( _parser.skips("for") ) {// instantiate variables as long as names are given
			needsep = true;
			if( _out ) {
				cout << "for";
				subgoal = strip_all(subgoal,subloc,[&](string_view const& v){
					auto o = gets_sym();
					if( o ) {
						cout << ' ' << *o;
					}
					return o;
				});
				_parser.skips(",");
				cout << ", ";
			} else {
				subgoal = strip_all(subgoal,subloc,[&](string_view const& v){ return gets_sym(); });
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
						_cout << _syntax->pretty_term(assm);
						if( !_parser.skips(",") ) break;
						_cout << ", ";
					}
					_parser.skip("]");
					_cout << " ] ";
				} else {
					auto cs = get_claim_status();
					auto assm = eat_assm(gets_term());
					add_claim(subloc,cs,assm);
					_cout << cs << _syntax->pretty_term(assm) << ", " << flush;
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
		if( needsep ) {
			_parser.skip(";");
			_cout << "show " << _syntax->pretty_cterm(subgoal) << endl;
			prover._prompt();
		}
		auto thesis = Inference::claim_exact(subloc,subgoal);
		auto thm = prover.proof_loop(thesis);
		if( thm ) {
			return thm->intro();
		}
		return {};
	}
	bool _thy_decl() {
		if( _parser.skips("theory") ) {
			string name = _parser.get(Parser::Word);
			auto loc = _thy.branch(name,"");
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
			auto loc = _thy.branch();
			Prover(*this,loc).deepen().loop();
			_thy.import( name, loc );
			_cout << "end namespace " << name << endl;
		} else if( _parser.skips("context") ) {
			string name = _parser.get();
			_parser.skip("begin");
			auto loc = find_thy(_thy,name);
			_cout << "in context " << name << endl;
			Prover(*this,loc).deepen().loop();
			_cout << "left " << name << endl;
		} else if ( _parser.skips("lemma") ||
			_parser.skips("theorem") ||
			_parser.skips("proposition")
		) {
			auto o = _state();
			if( _out && o ) {
				auto const& [cs,thm] = *o;
				cout << "proved " << cs << _syntax->pretty_thm(thm) << endl;
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
			_obtain();
		} else if( _parser.skips("define") ) {
			_define();
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
				if( _parser.skips(".") ) {
					return thesis.blast_all();
				}
				if( _parser.skips(",") ) {
					print_goal(thesis,"applied goals:\n\t");
				}
			} else if( bool dir = false; _parser.skips("unfold") || ( dir = true, _parser.skips("fold") ) ) {
				auto [rules,ctrl] = _get_rewrite(_thy,dir);
				_thy.rewriter().apply(rules,thesis,ctrl);
				if( _parser.skips(".") ) {
					return thesis.blast_all();
				}
				if( _parser.skips(",") ) {
					print_goal( thesis, dir ? "folded goal " : "unfolded goal " );
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
				_parser.skip(".");
				return thesis.blast_all(ctrl);
			} else if( _parser.skips(".") ) {
				auto thm = thesis.blast_all();
				return thm;
			} else if( _parser.skips("") ) {
				cerr << _parser.location() << ": Unexpected EOF" << endl;
				exit(0);
			} else if( _parser.skips("oops") ) {
				_cout << "oops" << endl;
				return {};
			} else {
				throw Error("unexpected")(_parser.get());
			}
			_prompt();
		} catch ( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _syntax->pretty_term(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
	}
	void loop() {
		for(;;) try {
			if( _stat() || _thy_decl() || _shared_decl() ) {
			} else if( _parser.skips("setup") ) {
				if( _parser.skips("rewrite") ) {
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					_cout << "registering rewriter:\n\timp: " << _syntax->pretty_thm(imp) <<
						"\n\trev: " <<  _syntax->pretty_thm(revimp) <<
						"\n\trefl: " << _syntax->pretty_thm(refl) <<
						"\n\ttrans: " << _syntax->pretty_thm(trans);
					_thy.rewriter().register_refl(refl).
						register_imp(imp,true).
						register_imp(revimp,false).
						register_trans(trans);
					_thy.find_thm( Rewriter::CONG, [&](AThm const& thm ){
						_thy.rewriter().register_cong(thm);
						_cout << "\n\tcong: " << _syntax->pretty_thm(thm);
						return false;
					} );
					_cout << endl;
				} else if( _parser.skips("refl") ) {
					_cout << "registering reflexivity: ";
					while( auto const& thm = gets_thm() ) {
						_thy.rewriter().register_refl(*thm);
						_cout << _syntax->pretty_thm(*thm);
					}
					_cout << endl;
				} else if( _parser.skips("trans") ) {
					_cout << "registering transitivity: ";
					while( auto const& thm = gets_thm() ) {
						_thy.rewriter().register_trans(*thm);
						_cout << _syntax->pretty_thm(*thm);
					}
					_cout << endl;
				} else if( _parser.skips("dual") ) {
					_cout << "registering dual: ";
					while( auto const& thm = gets_thm() ) {
						_thy.rewriter().register_dual(*thm);
						_cout << _syntax->pretty_thm(*thm);
					};
					_cout << endl;
				} else if( _parser.skips("define") ) {
					Thm const& beta = get_thm();
					_cout << " beta: " << _syntax->pretty_thm(beta) << endl;
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
					_syntax->opener("{",-1000,handler);
					_syntax->closer("}");
					_cout << "set up set comprehension" << endl;
				} else if( _parser.skips("print") ) {
					if( _parser.skips("ctxt_id") ) {
						_syntax->print_ctxt(true);
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
						_syntax->register_single_op(ch);
					} else {
						_syntax->register_multi_op(ch);
					}
					_cout << ' ' << sym;
				}
				_cout << endl;
			} else if( _parser.skips("prefix") ) {
				string sym = _parser.get();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(".");
				_make_own_parser();
				_syntax->prefix(sym,level,rlevel);
				_cout << "new prefix operator " << sym << endl;
			} else if( _parser.skips("infix") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(".");
				_make_own_parser();
				_syntax->infix(sym,level,llevel,rlevel);
				_cout << "new infix operator " << sym << endl;
			} else if( _parser.skips("binder") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				_parser.skip(".");
				_make_own_parser();
				_syntax->binder(sym,llevel,rlevel);
				_cout << "new binder " << sym << endl;
			} else if( _parser.skips("binder_middle") ) {
				string prefix = _parser.get();
				string mid = _parser.get();
				string sym = _parser.get();
				_parser.skip(".");
				_make_own_parser();
				_syntax->binder_mid(prefix,mid,sym);
				_cout << "new binder middle " << prefix << " x " << mid << " y. z := " << sym << " y (x. z)" << endl;
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
					_parser.skip(".");
					_cout << '.' << endl;
				} else if( _parser.skips("assume") ) {
					auto cs = get_claim_status();
					Thy var_loc = _thy.branch();
					for_variables([&]( auto& var ){ var_loc.fix(var); });
					CTerm assm = var_loc.enclose(get_term()).lift(_thy.cterm(ALL));
					Thm thm = cs.name ? _thy.add_assm(*cs.name,assm) : _thy.assume(assm);
					add_claim(_thy,cs,thm);
					_parser.skip(".");
					_cout << "assumed " << cs << _syntax->pretty_term(assm) << ". " << endl;
				} else if( _parser.skips("import") ) {
					import(true);
				} else if( _parser.skips("begin") ) {
					_parser.skips(".");
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
			cerr << _parser.location() << ": ERROR: " << _syntax->pretty_term(e) << endl;
			if( _exit_on_error ) exit(-1);
			_prompt();
		}
	}
	void _obtain() {
		string sym = get_sym();
		_parser.skip("where");
		_cout << "obtaining " << sym << " where" << endl;
		vector<CTerm> props;
		vector<Thm> prop_thms;
		auto thesis_loc = _thy.branch();
		CTerm var = thesis_loc.fix("?thesis");
		Ctxt goal_ctxt = thesis_loc.Ctxt::branch();
		goal_ctxt.fix(sym);
		auto props_loc = _thy.branch();
		props_loc.fix(sym);
		for(;;) {
			auto [cs,t] = get_assm();
			Thm thm = props_loc.assume(props_loc.branch().enclose(t).intro());
			add_claim(props_loc,cs,thm);
			prop_thms.push_back(thm);
			props.push_back(goal_ctxt.branch().enclose(t).intro());
			_cout << '\t' << cs << _syntax->pretty_term(thm) << endl;
			if( !_parser.skips(",") ) break;
		}
		_parser.skip(";");
		CTerm goal = var.weaken(goal_ctxt);
		for( auto& prop : ranges::reverse_view(props) ) {
			goal = prop >>= goal;
		}
		goal = goal.lift(thesis_loc.cterm(ALL)) >>= var;
		goal = goal.lift(_thy.cterm(ALL));
		_prompt();
		_cout << "prove " << _syntax->pretty_cterm(goal) << endl;
		auto thesis = Inference::claim_exact(_thy,goal);
		auto const& thm = Prover(*this,_thy).deepen().proof_loop(thesis);
		if( thm ) {
			auto [sym_term,deriver] = _thy.obtain(sym,*thm,make_spec_name(string(sym)));
			// der: ∀thesis. (p ⟹ ... ⟹ thesis) ⟹ thesis
			_cout << "obtained " << sym << endl;
			auto& intp = _thy.import("",props_loc);
			intp.instantiate(sym_term);
			for( auto const& prop_thm : prop_thms ) {
				auto const& arg = prop_thm.intro();// props... ⟹ prop_i
				Thm prop = deriver << arg;// prop_i
				intp.discharge(prop);
			}
			assert(intp.ready());
		}
	}
	Thy load_thy( Thy const& thy, string_view const& name ) {
		auto [fis,path] = file_of_thy(thy.dir(),name);
DEB(path);
		if( !fis.fail() ) {
			Lexer local_lexer(fis,path,*_syntax);
			auto base = thy;
			if( local_lexer.skips("base") ) {
				auto base_name = local_lexer.get();
				local_lexer.skip(".");
				base = find_thy(thy,base_name);
			} else {// Belong to the Root
				while( auto p = base.parent() ) {
					base = *p;
				}
			}
			cout << "loading " << base.dir() << name;
			string dir;// has dedicated directory or not
			if( filesystem::is_directory(base.dir()+name) ) {
				dir+=name;
				dir+='/';
				cout << '/';
			}
			cout << endl;
			auto sub = Prover(*this,base.branch(name,dir));
			sub.set_out(false);
			sub.set_lexer(local_lexer);
			sub.loop();
			return sub._thy;
		}
		if( auto gp = thy.parent() ) {
			return load_thy(*gp,name);
		}
		throw Error("\"theory not found\"")(name);
	}
	void move_to_thy( Thy const& thy ) {
		_thy = thy;
	}
private:
	void _make_own_parser() {
		if( !_own_parser ) {
//			_parser.fork();
			_own_parser = true;
		}
	}
};

void run( Lexer& lexer, Ref<Syntax>& syntax, string_view const& name, bool exit_on_error ) try {
	auto fis = fstream("Root.nl");
	if( !fis ) throw Error("\"Root not found\"");
	auto base_lexer = Lexer(fis,"Root.nl",*syntax);
	auto prover = Prover(base_lexer,syntax,true);
	prover.set_out(false);
	prover.loop();
	prover.set_lexer(lexer);
	cout << "loaded root theory." << endl;
	auto base = prover.thy();
	prover.set_out(true);
	prover._prompt();
	if( lexer.skips("base") ) {
		string base_ref = lexer.get();
		string_view view = base_ref;
		lexer.skip(".");
		for(;;) {
			auto p = view.find('.');
			if( p == string::npos ) break;
			base = prover.find_thy(base,view.substr(0,p));
			prover.move_to_thy(base);
			view = view.substr(p+1);
		}
		prover.move_to_thy(prover.find_thy(base,view));
		cout << "moving to " << name << endl;
		prover._prompt();
	}
	prover.enter_branch(name,"");
	prover.set_exit_on_error(exit_on_error);
	prover.loop();
} catch( Error const& e ) {
	cerr << e << endl;
	exit(-1);
}

int main(int argc, char* argv[]) {
	istream* pis;
	auto syntax = make_syntax();
	bool exit_on_error = false;
	if( argc == 1 ) {
		Lexer lexer(cin,"stdin",*syntax);
		run(lexer,syntax,"#stdin",false);
	} else {
		string name = argv[1];
		auto fin = fstream(name);
		Lexer lexer(fin,name,*syntax);
		run(lexer,syntax,name,true);
	}
	cout << "bye!" << endl;
	return 0;
}

