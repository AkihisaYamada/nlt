#include<fstream>
#include<ranges>
#include"locale.hpp"
#include"parser.hpp"
#include"definer.hpp"

using namespace std;

struct ClaimStatus {
	Opt<string> name;
	bool intro = false, force = false;
};

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.name ) {
		os << *cs.name;
	}
	if( cs.intro ) {
		os << "#intro";
	}
	return os << ": ";
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
	ret->register_multi_op('=');
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
	ret->infix(",",-1,-1,-2);
	ret->infix(";",-1,-1,-2);
	ret->infix(":=",-1,-1,-2);
	ret->prefix("if",-3,-2);
	ret->infix("then",-3,-2,-2);
	ret->infix("else",-3,-2,-2);
	return ret;
}

static Error const ProofMismatch = Error("#proof-mismatch");

class Prover {
	OptRef<Prover> _parent;
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
	Opt<Inference> _thesis;
	Mem<Rewriter> _rewriter;
	OptRef<Definer> _definer;
	bool _exit_on_error;
	bool _final = false;
	Prover( Prover& parent, Locale const& loc, Opt<Inference> thesis = {}, Opt<Path> const& path = {} ) :
		_parent(OptRef<Prover>::make(parent)),
		_depth(parent._depth),
		_loc(loc),
		_path(path),
		_syntax(parent._syntax),
		_parser(parent._parser.get_lexer(),*parent._syntax),
		_own_parser(false),
		_thesis(thesis),
		_rewriter(parent._rewriter),
		_definer(parent._definer),
		_exit_on_error(parent._exit_on_error) {
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
	static Error const UnfinishedProof() {
		return Error("#unfinished_proof");
	}
	Prover( Lexer& lexer, Ref<Syntax> syntax, bool exit_on_error ) :
		_depth(0),
		_path({"","Root"}),
		_loc(),
		_syntax(syntax),
		_parser(lexer,*_syntax),
		_own_parser(true),
		_exit_on_error(exit_on_error),
		_rewriter(Mem<Rewriter>::make()) {
		_prompt();
	}
	Prover& deepen() & {
		_depth++;
		return *this;
	}
	Prover&& deepen() && {
		_depth++;
		return std::move(*this);
	}
	void set_exit_on_error( bool b ) {
		_exit_on_error = b;
	}
	Prover branch( string_view const& name ) {
		auto loc = _loc.branch(name);
		if( _path ) {
			return Prover( *this, loc, {}, {{_path->dir+"/"+_path->name,name}});
		} else {
			return Prover( *this, loc, {}, {} );
		}
	}
	Lexer& get_lexer() & {
		return _parser.get_lexer();
	}
	void set_lexer( Lexer& lexer ) {
		_parser.set_lexer(lexer);
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
	pair<Rewriter::Rules,Rewriter::Ctrl> _get_rewrite( Locale& loc, bool rev = false ) {
		pair<Rewriter::Rules,Rewriter::Ctrl> ret = {_rewriter->make_rules(),{}};
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
			_rewriter->add_rule( loc, rules, *arg, _parser.skips("-") ? !rev : rev );
			n++;
		}
		if( ctrl.max < n ) {
			ctrl.max = n;
		}
		return ret;
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
					ret = _rewriter->rewrite(rules,loc,ret,ctrl);
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
	void _flush() {
		cout << flush;
	}
	ostream& _indent() {
		for( int i = 0; i <= _depth; i++ ) {
			cout << '>';
		}
		return cout << ' ';
	}
	Prover& _prompt() & {
		_indent() << flush;
		return *this;
	}
	Prover&& _prompt() && {
		_indent() << flush;
		return std::move(*this);
	}
	Opt<CTerm> has_goal() {
		if( _thesis ) {
			return _thesis->has_goal();
		}
		return {};
	}
	ClaimStatus get_claim_status() {
		ClaimStatus cs;
		cs.name = _parser.gets_thm_name();
		while( _parser.skips("#") ) {
			if( _parser.skips("intro") ) {
				cs.intro = true;
			} else if( _parser.skips("concl") ) {
				cs.force = true;
			} else {
				throw Error("\"unknown #\"");
			}
		}
		if( _parser.skips("!") ) {
			cs.force = true;
		} else {
			_parser.skip(":");
		}
		return cs;
	}
	pair<ClaimStatus,Term> get_assm() {
		if( _parser.skips("[") ) {
			auto t = get_term();
			_parser.skips("]");
			return {{{},false,true},t};
		}
		return {get_claim_status(),get_term()};
	}
	void add_claim( Locale& loc, ClaimStatus cs, Thm const& thm ) {
		if( cs.intro ) {
			loc.add_thm(Inference::INTRO,thm);
		}
		if( cs.force ) {
			add_forced(loc,thm,true);
		}
		if( cs.name ) {
			loc.add_thm(*cs.name,thm);
		}
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
	void print_goal( string pre = "goal " ) {
		assert( _thesis );
		Term acc = _thesis->thm();
		size_t i = 0;
		while( i < _thesis->goal_count() ) {
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
	Thm proof_loop() {
		auto ret = loop();
		if( !ret ) {
			throw Error("no_proof");
		}
		return *ret;
	}
	void for_variables( function<void( string const& v )> act ) {
		if( _parser.skips("for") ) {
			cout << "for" << flush;
			while( auto const& sym = gets_sym() ) {
				cout << ' ' << *sym << flush;
				act(*sym);
			}
			_parser.skip(",");
			cout << ", ";
		}
	}
	/** Creates a nested locale, where outer one fixes free variables, and 
	 * inner locale collects assumptions.
	 */
	pair<Prover,CTerm> get_statement() {
		auto var_loc = _loc.branch();
		auto assm_loc = var_loc.branch();
		auto ret = Prover(*this,assm_loc);
		for_variables([&](auto const& v){ var_loc.fix(v); });
		if( _parser.skips("if") ) {
			cout << "if " << flush;
			auto add_assm = [&]( Term const& t ) {
				return assm_loc.assume(var_loc.enclose(t).weaken(assm_loc));
			};
			for(;;) {
				if( _parser.skips("[") ) {
					cout << "[ ";
					for(;;) {
						auto t = get_term();
						cout << t;
						add_forced(assm_loc,add_assm(t),true);
						if( !_parser.skips(",") ) break;
						cout << ", ";
					}
					_parser.skip("]");
					cout << " ] ";
				} else {
					auto [cs,t] = get_assm();
					add_claim(assm_loc,cs,add_assm(t));
					cout << cs << _syntax->pretty_term(t) << ", " << flush;
				}
				if( !_parser.skips(",") ) break;
			};
			_parser.skip("then");
			cout << "then ";
		}
		Term conc = _parser.get_term(0);
		_parser.skip(":=");
		CTerm goal = var_loc.enclose(conc).weaken(assm_loc);
		cout << _syntax->pretty_cterm(goal) << endl;
		ret._thesis = Inference::claim_exact(assm_loc,goal);
		ret.deepen()._prompt();
		return {ret,goal};
	}
	void import( bool mod ) {
		string prefix;
		string name = _parser.get_thm_name();
		if( _parser.skips(":") ) {
			prefix = name;
			name = _parser.get();
		}
		auto loc = find_locale(name);
		auto& intp = _loc.import(prefix,loc);
		while( auto const& t = _parser.gets_term(1000) ) {
			while( intp.discharges(mod) || intp.retains() );
			auto const& fix = intp.fixing();
			if( !fix ) {
				throw Error("\"too many instantiation\"")(*t);
			}
			auto v = *fix;
			if( *t == "_" ) {
				auto t = _loc.constant(v);
				if( t ) intp.instantiate(*t);
				else if( mod ) intp.instantiate(_loc.fix(v));
				else throw Error("\"instantiation must be specified\"")(v);
			} else {
				intp.instantiate( mod ? _loc.cterm(*t) : _loc.enclose(*t) );
			}
		}
		if( _parser.skips(":=") ) {
			_depth++;
			for(;;){
				if( auto x = intp.fixing() ) {
					cout << "Instantiate " << *x << endl;
				} else if( auto x = intp.assuming() ) {
					auto [name,axiom] = *x;
					cout << "Discharge " << name << ": " << _syntax->pretty_cterm(axiom) << endl;
				} else if( auto x = intp.obtaining() ) {
					cout << "Retain " << x->sym << " in " << _syntax->pretty_cterm(x->spec) << endl;
				} else {
					cout << "Completed" << endl;
				}
				_indent();
				if( _parser.skips("instantiate") ) {
					while( intp.discharges(mod) || intp.retains() );
					auto x = intp.fixing();
					if( !x ) throw Error("\"unexpected instantiate\"");
					if( auto t = _parser.gets_term() ) {
						intp.instantiate( mod ? _loc.cterm(*t) : _loc.enclose(*t) );
						cout << "for " << _syntax->pretty_term(*t) << endl;
					} else {
						auto c = _loc.constant(*x);
						if( c ) intp.instantiate(*c);
						else if( mod ) intp.instantiate(_loc.fix(*x));
						else throw Error("\"instantiation must be specified\"")(*x);
					}
					_parser.skip(";");
				} else if( _parser.skips("-") ) {
					cout << "discharge ";
					if( _parser.skips("know") ) {
						_parser.skip(";");
						while( intp.instantiates(mod) || intp.retains() );
						intp.discharge();
					} else if( mod && _parser.skips("assume") ) {
						_parser.skip(";");
						while( intp.instantiates(mod) || intp.retains() );
						auto a = intp.assuming();
						if( !a ) throw Error("\"unexpected discharge\"");
						auto [name,axiom] = *a;
						Thm thm = _loc.add_assm(name,axiom);
						intp.discharge(thm);
						cout << "Assumed " << _syntax->pretty_thm(thm) << endl;
					} else {
						auto [prover,concl] = get_statement();
						auto const& claim = concl.intro();
						auto const& var_loc = *prover._loc.parent();
						for(;;) {
							while( intp.instantiates(mod) || intp.retains() );
							auto a = intp.assuming();
							if( !a ) {
								throw Error("\"no matching discharge\"")(claim);
							}
							auto [name,axiom] = *a;
							auto axiom_vars = axiom.ctxt().branch();
							auto goal = strip_all(axiom,axiom_vars);
							auto m = match(claim,goal,[&](auto v){ return var_loc.fixes(v); });
							if( !m ) {
								if( intp.discharges(mod) ) continue;
								throw Error("\"failed to discharge\"")(goal);
							}
							auto const& thm = prover.proof_loop().intro();
							auto local_intp = Intp(var_loc,axiom_vars);
							subst_intp(local_intp,*m);
							intp.discharge(local_intp.subst(thm).intro());
							break;
						}
					}
				} else if( _parser.skips("obtain") ) {
					obtain();
				} else if( _parser.skips("retain") ) {
					while( intp.discharges(mod) || intp.instantiates(mod) );
					auto x = intp.obtaining();
					if( !x ) throw Error("\"unexpected retain\"");
					auto sym = x->sym;
					if( _parser.skips(";") ) {
					} else {
						sym = _parser.get();
						_parser.skip(";");
					}
					auto [sym_term,spec] = _loc.obtain(sym,x->ex,x->spec_name);
					intp.retain(sym_term,spec);
				} else if( _parser.skips("substitute") ) {
					while( intp.discharges(mod) || intp.instantiates(mod) );
					auto x = intp.obtaining();
					if( !x ) throw Error("\"unexpected substitute\"");
					auto sym = x->sym;
					Locale thesis_loc = _loc.branch();
					auto term = thesis_loc.cterm(_parser.get_term());
					_parser.skip(":=");
					CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
						return _loc.constant(x);
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
					auto const& spec = Prover(*this,thesis_loc,thesis).deepen().proof_loop().intro();
// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
					intp.retain(_loc.cterm(term),spec);
				} else {
					_parser.skip("done");
					_depth--;
					break;
				}
			}
		} else {
			while( intp.instantiates(mod) || intp.discharges(mod) || intp.retains() );
		}
		_parser.skip(";");
		cout << (mod ? "imported " : "interpreted ") << name << endl;
	}
	set<Intro> get_rules() {
		set<Intro> rules;
		for(;;) {
			if( _parser.skips("!") ) {
				auto thm = get_thm();
				rules.emplace(Intro::axiom(thm));
				continue;
			}
			if( auto thm = gets_thm() ) {
				rules.emplace(Intro::rule(*thm));
				continue;
			}
			break;
		}
		return rules;
	}
	Opt<Thm> loop() {
		for(;;) try {
			if( _parser.skips("include") ) {
				load_locale(_parser.get_thm_name(),true);
				_parser.skip(";");
			} else if( _parser.skips("locale") ) {
				string name = _parser.get();
				auto loc = _loc.branch(name);
				while( auto sym = gets_sym() ) {
					loc.fix(*sym);
				}
				if( _parser.skips(":=") ) {
					cout << "Creating locale " << name << endl;
					Prover(*this,loc,{},{}).deepen()._prompt().loop();
					cout << "end locale " << name << endl;
				}
				_parser.skip(";");
			} else if( _parser.skips("interpret") ) {
				import(false);
			} else if( _parser.skips("ctxt") ) {
				if( _parser.skips(";") ) {
					cout << _loc.pretty(*_syntax) << endl;
				} else {
					string name = _parser.get();
					_parser.skip(";");
					auto loc = find_locale(name);
					cout << loc.pretty(*_syntax) << endl;
				}
			} else if( _parser.skips("in") ) {
				string name = _parser.get();
				_parser.skip("{");
				cout << "in " << name << endl;
				auto loc = find_locale(name);
				auto sub = Prover(*this,loc).deepen().loop();
				_parser.skip("}");
				cout << "left " << name << endl;
			} else if( _parser.skips("thm") ) {
				string pref = "thm ";
				do {
					Thm thm = get_thm();
					cout << pref << _syntax->pretty_thm(thm) << ';' << endl;
					pref = "\t";
				} while( !_parser.skips(";") );
			} else if( _parser.skips("term") ) {
				Term term = get_term();
				_parser.skip(";");
				cout << "term " << _syntax->pretty_term(term) << endl;
			} else if( _parser.skips("note") ) {
				auto cs = get_claim_status();
				auto thm = get_thm();
				add_claim(_loc,cs,thm);
				cout << "note " << cs << _syntax->pretty_thm(thm) << endl;
				while( auto o = gets_thm() ) {
					add_claim(_loc,cs,*o);
					cout << "\t" << cs << _syntax->pretty_thm(*o) << endl;
				}
				_parser.skip(";");
			} else if(
				_thesis ? _parser.skips("show") :
					_parser.skips("lemma") ||
					_parser.skips("theorem")
			) {
				auto cs = get_claim_status();
				cout << "Showing " << cs << flush;
				auto [prover,goal] = get_statement();
				auto thm = prover.proof_loop().intro().intro();
				add_claim(_loc,cs,thm);
				if( _thesis ) {
					print_goal();
				} else {
					cout << "proved " << cs << _syntax->pretty_thm(thm) << endl;
				}
			} else if( _parser.skips("obtain") ) {
				obtain();
			} else if( _parser.skips("define") ) {
				Opt<string> name_op;
				if( _parser.skips("(") ) {
					name_op = _parser.get();
					_parser.skip(")");
				}
				Term l = get_term();
				_parser.skip(":=");
				Term r = get_term();
				_parser.skip(";");
				if( !_definer ) {
					throw Error("definer not setup");
				}
				auto [f,spec] = _definer->define(_loc,l,r,name_op);
				Thm def = spec << _loc.thm("imp.refl");
				string name = name_op ? *name_op : f + "_def";
				_loc.add_thm(name,def);
				cout << "Defined " << name << ": " << _syntax->pretty_term(l) << " := " << _syntax->pretty_term(r) << endl;
			} else if( _parser.skips("prefix") ) {
				string sym = _parser.get();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(";");
				_make_own_parser();
				_syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( _parser.skips("infix") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				int level = _parser.get_int();
				_parser.skip(";");
				_make_own_parser();
				_syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else if( _parser.skips("binder") ) {
				string sym = _parser.get();
				int llevel = _parser.get_int();
				int rlevel = _parser.get_int();
				_parser.skip(";");
				_make_own_parser();
				_syntax->binder(sym,llevel,rlevel);
				cout << "New binder " << sym << endl;
			} else if( _parser.skips("binder_middle") ) {
				string prefix = _parser.get();
				string mid = _parser.get();
				string sym = _parser.get();
				_parser.skip(";");
				_make_own_parser();
				_syntax->binder_mid(prefix,mid,sym);
				cout << "New binder middle " << prefix << " x " << mid << " y. z := " << sym << " y (x. z)" << endl;
			} else if( _parser.skips("setup") ) {
				if( _parser.skips("rewrite") ) {
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					cout << "Registering rewriter:\n\timp: " << _syntax->pretty_thm(imp) <<
						"\n\trev: " <<  _syntax->pretty_thm(revimp) <<
						"\n\trefl: " << _syntax->pretty_thm(refl) <<
						"\n\ttrans: " << _syntax->pretty_thm(trans) << endl;
					_rewriter->register_refl(refl);
					_rewriter->register_imp(imp,true);
					_rewriter->register_imp(revimp,false);
					_rewriter->register_trans(trans);
				} else if( _parser.skips("refl") ) {
					cout << "Registering reflexivity: ";
					while( auto const& thm = gets_thm() ) {
						_rewriter->register_refl(*thm);
						cout << _syntax->pretty_thm(*thm);
					}
					cout << endl;
				} else if( _parser.skips("trans") ) {
					cout << "Registering transitivity: ";
					while( auto const& thm = gets_thm() ) {
						_rewriter->register_trans(*thm);
						cout << _syntax->pretty_thm(*thm);
					}
					cout << endl;
				} else if( _parser.skips("dual") ) {
					cout << "Registering dual: ";
					while( auto const& thm = gets_thm() ) {
						_rewriter->register_dual(*thm);
						cout << _syntax->pretty_thm(*thm);
					};
					cout << endl;
				} else if( _parser.skips("cong") ) {
					cout << "Registering congruence:";
					while( auto const& thm = gets_thm() ) {
						_rewriter->register_cong(*thm);
						cout << "\n\t" << _syntax->pretty_thm(*thm);
					};
					cout << endl;
				} else if( _parser.skips("define") ) {
					Thm const& beta = get_thm();
					cout << " beta: " << _syntax->pretty_thm(beta) << endl;
					_definer = OptRef<Definer>::make(_loc,_rewriter,beta);
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
					_syntax->opener("{",-1000,handler);
					_syntax->closer("}");
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
					string const& sym = _parser.get();
					int ch = int_of_chars(sym.data());
					if( solo ) {
						_syntax->register_single_op(ch);
					} else {
						_syntax->register_multi_op(ch);
					}
					cout << ' ' << sym;
				}
				cout << endl;
			} else if( _parser.skips("end") || _parser.skips("") ) {
				return {};
			} else if( _thesis ) {
				if( _parser.skips("goal") ) {
					_parser.skip(";");
					print_goal();
				} else if( _parser.skips("apply") ) {
					int min, max;
					bool safe, deep;
					if( _parser.skips("+") ) {
						min = 1; max = 255; safe = false; deep = true;
					} else {
						min = max = 1; safe = true; deep = false;
					}
					auto rules = get_rules();
					_parser.skip(";");
					_thesis->apply(rules,min,max,safe,deep);
					print_goal("applied goals:\n\t");
				} else if( bool dir = false; _parser.skips("unfold") || ( dir = true, _parser.skips("fold") ) ) {
					auto [rules,ctrl] = _get_rewrite(_loc,dir);
					_parser.skip(";");
					_rewriter->apply(rules,*_thesis,ctrl);
					print_goal( dir ? "unfolded goal " : "folded goal " );
				} else if( _parser.skips("-") ) {
					auto goal = has_goal();
					if( !goal ) {
						throw Error("\"unexpected subgoal\"");
					}
					auto subprf = Prover(*this,_loc.branch()).deepen();
					CTerm newgoal = goal->weaken(subprf._loc);
					cout << "subgoal ";
					bool needsep = false;
					if( _parser.skips("for") ) {// instantiate variables as long as names are given
						needsep = true;
						cout << "for";
						newgoal = strip_all(newgoal,subprf._loc,[&](string_view const& v)->Opt<string> {
							auto o = gets_sym();
							if( o ) {
								cout << ' ' << *o;
							}
							return o;
						});
						_parser.skips(",");
						cout << ", ";
					}
					if( _parser.skips("if") ) {
						needsep = true;
						cout << "if ";
						auto eat_assm = [&]( Term const& t ){
							auto imp = newgoal.cbinary(IMP);
							if( !imp ) throw Error("\"unexpected assumption\"")(t);
							newgoal = imp->second;
							if( imp->first != t ) throw Error("\"assumption mismatch\"")(imp->first)(t);
							return subprf._loc.assume(subprf._loc.enclose(t));
						};
						for(;;) {
							if( _parser.skips("[") ) {
								cout << "[ ";
								for(;;) {
									auto assm = eat_assm(get_term());
									add_forced(subprf._loc,assm,true);
									cout << _syntax->pretty_term(assm);
									if( !_parser.skips(",") ) break;
									cout << ", ";
								}
								_parser.skip("]");
								cout << " ] ";
							} else {
								auto [cs,t] = get_assm();
								add_claim(subprf._loc,cs,eat_assm(t));
								cout << cs << _syntax->pretty_term(t) << ", " << flush;
							}
							if( !_parser.skips(",") ) break;
						};
						if( _parser.skips("then") ) {
							if( _parser.get_term() != newgoal ) {
								throw Error("\"conclusion mismatch\"")(newgoal);
							}
						}
					}
					if( needsep ) {
						_parser.skip(":=");
						cout << "then ";
					}
					cout << _syntax->pretty_cterm(newgoal) << endl;
					subprf._thesis = Inference::claim_exact(subprf._loc,newgoal);
					_thesis->discharge(subprf._prompt().proof_loop().intro());
					print_goal("next goal ");
				} else if( _parser.skips("just") ) {
					set<Intro> rules;
					for(;;) {
						if( auto thm = gets_thm() ) {
							rules.emplace(Intro::axiom(*thm));
							continue;
						}
						break;
					}
					_parser.skip(";");
					size_t fuel = 255;
					while( _thesis->goal_count() > 0 ) {
						if( fuel == 0 ) throw Error("\"excessive just\"");
						_thesis->apply(rules);
						fuel--;
					}
					return _thesis->concluding();
				} else if( _parser.skips("done") ) {
					_parser.skip(";");
					size_t fuel = 255;
					while( _thesis->goal_count() > 0 ) {
						_thesis->blast(fuel,0);
					}
					return _thesis->concluding();
				} else if( _parser.skips("by") ) {
					auto intros = get_rules();
					set<Elim> elims;
					function<bool(Inference&)> extra = [&](auto){ return false; };
					size_t fuel = 255;
					while( _parser.skips("#") ) {
						if( _parser.skips("elim") ) {
							while( auto elim = gets_thm() ) {
								elims.emplace(Elim::rule(*elim));
							}
						} else if( bool dir = false; _parser.skips("unfold") || (dir = true, _parser.skips("fold") ) ) {
							auto [rrules,ctrl] = _get_rewrite(_loc,dir);
							extra = [rrules,ctrl,this](Inference& thesis){
								return _rewriter->applies(rrules,thesis,ctrl);
							};
						} else {
							throw Error("\"unexpected\"")(_parser.peek_token());
						}
					}
					_parser.skip(";");
					while( _thesis->goal_count() > 0 ) {
						_thesis->blast(fuel,1,intros,elims,extra);
					}
					return _thesis->concluding();
				} else if( _parser.skips("sorry") ) {
					_parser.skip(";");
					throw Error("sorry");
				} else {
					throw Error("unexpected")(_parser.get());
				}
			} else if( !_final ) {
				if( _parser.skips("fix") ) {
					cout << "Fixing";
					for(;;) {
						if ( auto sym = gets_sym() ) {
							cout << ' ' << _loc.fix(*sym) << flush;
						} else {
							break;
						}
					}
					_parser.skip(";");
					cout << ';' << endl;
				} else if( _parser.skips("assume") ) {
					auto cs = get_claim_status();
					Locale var_loc = _loc.branch();
					for_variables([&]( auto& var ){ var_loc.fix(var); });
					CTerm assm = var_loc.enclose(get_term()).lift(_loc.cterm(ALL));
					Thm thm = cs.name ? _loc.add_assm(*cs.name,assm) : _loc.assume(assm);
					add_claim(_loc,cs,thm);
					_parser.skip(";");
					cout << "Assumed " << cs << _syntax->pretty_term(assm) << "; " << endl;
				} else if( _parser.skips("import") ) {
					import(true);
				} else if( _parser.skips("finalize") ) {
					_parser.skip(";");
					_final = true;
					cout << "Finalized" << endl;
				} else {
					throw Error("unexpected")(_parser.get());
				}
			} else {
				throw Error(Term("unexpected")(_parser.get()));
			}
			_prompt();
		} catch ( ::Error const& e ) {
			cerr << _parser.location() << ": ERROR: " << _syntax->pretty_term(e.term) << endl;
			_error();
		} catch ( exception const& e ) {
			cerr << _parser.location() << ": Other exception: " << e.what() << endl;
			_error();
		}
	}
	void obtain() {
		string sym = _parser.get();
		_parser.skip("where");
		cout << "Obtaining " << sym << " where ";
		vector<ClaimStatus> names;
		vector<Term> props;
		for(;;) {
			auto [cs,t] = get_assm();
			names.push_back(cs);
			props.push_back(t);
			cout << cs << ": " << _syntax->pretty_term(t) << ", ";
			if( !_parser.skips(",") ) break;
		}
		_parser.skip(":=");
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
		Opt<Inference> bak = _thesis;
		auto const& thm = Prover(*this,_loc,Inference::claim_exact(_loc,goal)).deepen()._prompt().proof_loop();
		auto [sym_term,spec] = _loc.obtain(sym,thm,make_spec_name(string(sym)));
		cout << "Obtained " << sym << " where ";
		// register properties
		auto all = spec.cbinder(ALL);
		assert(all);
		auto imp = all->second.cbinary(IMP);
		assert(imp);
		auto subst = CSubst(spec.ctxt());// to remove thesis
		Thm refl = _loc.thm("imp.refl");// P ⟹ P
		Thm weaken = _loc.thm("weaken");// (P ⟹ Q) ⟹ P
		Thm ignore = _loc.thm("ignore");// ((P ⟹ Q) ⟹ R) ⟹ Q ⟹ R
		CTerm s = imp->first;// prop ⟹ props ⟹ var
		auto imp2 = s.cbinary(IMP);
		s = imp2->second;// props... ⟹ var
		for(auto name_it = names.begin();;) {
			if( name_it == names.end() ) {
				throw Error("\"too few names for obtain\"")(sym);
			}
			if( auto imp3 = s.cbinary(IMP) ) {// more props follow
				s = imp3->second;// props... ⟹ var
				Thm prop = spec << weaken;
				add_claim(_loc,*name_it,prop);
				cout << *name_it << ": " << prop << endl << "\t";
				spec = ignore << spec;// ∀var. (props... ⟹ var) ⟹ var
				name_it++;
			} else {// spec: ∀var. (P ⟹ var) ⟹ var
				Thm prop = spec << refl;
				add_claim(_loc,*name_it,prop);
				cout << *name_it << ": " << prop << ';' << endl;
				break;
			}
		}
	}
	void load_locale( string_view const& name, bool open = false ) {
		if( _path ) {
			string dir = _path->dir + _path->name + "/";
			auto fis = file_of_locale(dir,name);
			if( !fis.fail() ) {
				auto& prev = get_lexer();
				Lexer local_lexer(fis,dir+name,*_syntax);
				local_lexer.skip("base");
				auto parent_name = local_lexer.get();
				local_lexer.skip(";");
				cout << "Loading " << name << endl;
				if( open ) {
					auto prev_loc = _loc;
					_loc = _loc.branch(name);
					set_lexer(local_lexer);
					_indent();
					loop();
					set_lexer(prev);
					_loc = prev_loc;
				} else {
					Prover sub = Prover(*this,_loc.branch(name),{},{{dir,name}}).deepen();
					sub.set_lexer(local_lexer);
					sub._indent();
					sub.loop();
				}
				return;
			}
		}
		if( _parent ) {
			_parent->load_locale(name);
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
		string const& base_name = lexer.get();
		lexer.skip(";");
		auto fis = file_of_locale("Root/",base_name);
		if( fis.fail() ) {
			cerr << "could not find base " << base_name << endl;
			exit(-1);
		}
		auto local_lexer = Lexer(fis,base_name,*syntax);
		Prover base = preload(local_lexer,syntax,base_name,true);
		base.loop();
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
		auto fin = fstream(name);
		Lexer lexer(fin,name,*syntax);
		preload(lexer,syntax,name,true).loop();
	}
	cout << "bye!" << endl;
	return 0;
}

