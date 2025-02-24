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
	ret->register_multi_op('=');
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
	ret->infix(":=",-1,-1,-2);
	ret->prefix("if",-3,-2);
	ret->infix("then",-3,-2,-2);
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
	Concluder _concluder;
	Mem<Rewriter> _rewriter;
	set<Thm> _forced_intros;
	OptRef<Definer> _definer;
	bool _exit_on_error;
	bool _final = false;
	Prover(Prover& parent, Locale const& loc, Opt<Path> const& path = {}, Opt<Inference> thesis = {}) :
		_parent(OptRef<Prover>::make(parent)),
		_depth(parent._depth),
		_loc(loc),
		_path(path),
		_syntax(parent._syntax),
		_parser(parent._parser.get_lexer(),*parent._syntax),
		_own_parser(false),
		_thesis(thesis),
		_concluder(parent._concluder),
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
			return Prover( *this, loc, {{_path->dir+"/"+_path->name,name}});
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
	void _rewrite( Locale& loc, Opt<Thm&> thm, vector<char> pos, size_t min, size_t max, bool safe, bool rev = false ) {
		auto rel = [&]()->Opt<string>{
			if( _parser.skips("(") ) {
				string ret = _parser.get_token();
				_parser.skip(")");
				return ret;
			}
			return {};
		}();
		if( _parser.skips("[") ) {// parse position
			while( !_parser.skips("]") ) {
				pos.push_back(_parser.get_int());
			}
		}
		if( _parser.skips("*") ) {
			min = 0; max = 255; safe = false;
		} else if( _parser.skips("+") ) {
			min = 1; max = 255; safe = false;
		} else {
			min = 1; max = 1; safe = true;
		}
		Rewriter::Rules rules = _rewriter->make_rules();
		while( auto const& arg = _gets_thm(loc) ) {
			_rewriter->add_rule(rules,*arg,rev);
		}
		if( thm ) {
			*thm = _rewriter->rewrite(rules,*thm,min,max,safe,pos,rel);
		} else {
			_rewriter->apply(rules,*_thesis,min,max,safe,pos,rel);
		}
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
					_rewrite(loc,ret,{},1,1,true,false);
				} else if( _parser.skips("folded") ) {
					_rewrite(loc,ret,{},1,1,true,true);
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
	Opt<string> gets_sym() {
		if( _parser.skips("(") ) {
			auto const& ret = _parser.get_token();
			_parser.skip(")");
			return ret;
		} else {
			return _parser.gets(Tokenizer::Word);
		}
	}
	void get_named_terms( function<void(Opt<string> const&, Term const&, bool)> const& f ) {
		for(;;) {
			auto const& name = _parser.gets_thm_name();
			bool force = _parser.skips("!");
			if( !force ) {
				if( !name ) {
					return;
				}
				_parser.skip(":");
			}
			f(name,_parser.get_term(0),force);
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
			_loc.add_thm(CONCL,thm);
		}
		if( cs.name ) {
			_loc.add_thm(*cs.name,thm);
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
	void print_goal() {
		assert( _thesis );
		Term acc = _thesis->thm();
		size_t i = 0;
		string pre = "goal ";
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
	void for_variables( Locale& var_loc ) {
		if( _parser.skips("for") ) {
			cout << "for" << flush;
			while( auto const& sym = gets_sym() ) {
				cout << ' ' << *sym << flush;
				var_loc.fix(*sym);
			}
			_parser.skip(",");
			cout << ", ";
		}
	}
	Prover prove(Locale const& loc, CTerm const& goal) {
		return Prover(*this,loc,{},Inference(loc,goal)).deepen()._prompt();
	}
	/** Creates a nested locale, where outer one fixes free variables, and 
	 * inner locale collects assumptions.
	 */
	pair<Prover,CTerm> get_statement() {
		auto var_loc = _loc.branch();
		auto assm_loc = var_loc.branch();
		auto ret = Prover(*this,assm_loc);
		for_variables(var_loc);
		if( _parser.skips("if") ) {
			cout << "if " << flush;
			get_named_terms([&]( Opt<string> const& name, Term const& t, bool force ){
				CTerm ct = var_loc.enclose(t).weaken(assm_loc);
				if( name ) {
					cout << *name;
					Thm assm = assm_loc.assume(*name,ct);
					if( force ) {
						cout << "! ";
						assm_loc.add_thm(INTRO,assm);
					} else {
						cout << ": ";
					}
				} else {
					if( force ) {
						cout << "! ";
						assm_loc.assume(INTRO,ct);
					} else {
						assm_loc.assume(ASSM,ct);
					}
				}
				cout << _syntax->pretty_term(t) << ", " << flush;
			});
			_parser.skip("then");
			cout << "then ";
		}
		Term conc = _parser.get_term(0);
		_parser.skip(":=");
		CTerm goal = var_loc.enclose(conc).weaken(assm_loc);
		cout << _syntax->pretty_cterm(goal) << endl;
		ret._thesis = Inference(assm_loc,goal);
		ret.deepen()._prompt();
		return {ret,goal};
	}
	Thm note() {
		auto goal_loc = _loc.branch();
		vector<pair<string,CTerm>> assms;
		if( _parser.skips("for") ) {
			while( auto const& sym = gets_sym() ) {
				goal_loc.fix(*sym);
			}
			_parser.skip(",");
		}
		if( _parser.skips("if") ) {
			get_named_terms([&]( Opt<string> const& s, Term const& t, bool forced ){
				if( !s ) throw Error("missing name");
				assms.emplace_back(*s,goal_loc.enclose(t));
			});
			_parser.skip("then");
		}
		for( auto [name,assm] : assms ) {
			goal_loc.assume(name,assm);
		}
		swap(goal_loc,_loc);
		Thm ret = get_thm().intro();
		_parser.skip(";");
		swap(goal_loc,_loc);
		return ret;
	}
	void import( bool mod ) {
		string prefix;
		string name = _parser.get_thm_name();
		if( _parser.skips(":") ) {
			prefix = name;
			name = _parser.get_token();
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
				if( auto const& fix = intp.fixing() ) {
					auto v = *fix;
					cout << "Instantiate " << v << endl;
					_indent();
					if( _parser.skips("instantiate") ) {
						for(;;) {
							if( _parser.skips("_") ) {
								auto t = _loc.constant(v);
								if( t ) intp.instantiate(*t);
								else if( mod ) intp.instantiate(_loc.fix(v));
								else throw Error("\"instantiation must be specified\"")(v);
							} else if( auto t = _parser.gets_term(1000) ) {
								intp.instantiate( mod ? _loc.cterm(*t) : _loc.enclose(*t) );
								cout << "for " << _syntax->pretty_term(*t) << endl;
							} else {
								break;
							}
							if( auto const& fix = intp.fixing() ) {
								v = *fix;
							} else {
								break;
							}
						}
						_parser.skip(";");
					} else {
						if( !intp.instantiates(mod) ) {
							throw Error("\"failed to instantiate\"")(v);
						}
					}
				} else if( auto a = intp.assuming() ) {
					auto [name,axiom] = *a;
					cout << "Discharge " << name << ": " << _syntax->pretty_cterm(axiom) << endl;
					_indent();
					if( _parser.skips("know") ) {
						_parser.skip(";");
						intp.discharge();
					} else if( _parser.skips("discharge") ) {
						cout << "discharge ";
						auto [prover,concl] = get_statement();
						auto const& claim = concl.intro();
						auto const& var_loc = *prover._loc.parent();
						auto axiom_vars = axiom.ctxt().branch();
						auto const& goal = strip_all(axiom,axiom_vars);
						auto const& m = match(claim,goal,[&](auto v){ return var_loc.fixes(v); });
						if( !m ) {
							throw Error("\"unmatching discharge\"")(claim)(axiom);
						}
						auto const& thm = prover.proof_loop();
						auto local_intp = Intp(var_loc,axiom_vars);
						subst_intp(local_intp,*m);
						intp.discharge(local_intp.subst(thm).intro());
					} else if( mod && _parser.skips("assume") ) {
						_parser.skip(";");
						Thm thm = _loc.assume(name,axiom);
						intp.discharge(thm);
						cout << "Assumed " << _syntax->pretty_thm(thm) << endl;
					} else {
						if( !intp.discharges(mod) ) {
							throw Error("\"failed to discharge\"")(name)(axiom);
						}
					}
				} else if( auto obtain = intp.obtaining() ) {
					string sym = obtain->sym;
					cout << "Obtain " << sym << " in " << _syntax->pretty_cterm(obtain->spec) << endl;
					_indent();
					if( _parser.skips("obtain") ) {
						if( _parser.skips(";") ) {
						} else {
							sym = _parser.get_token();
							_parser.skip(";");
						}
						auto [sym_term,spec] = _loc.obtain(sym,obtain->ex,obtain->spec_name);
						intp.retain(sym_term,spec);
					} else if( _parser.skips("retain") ) {
						if( !_parser.skips(";") ) {
							sym = _parser.get_token();
							_parser.skip(";");
						}
						intp.retain(_loc.cterm(sym));
					} else if( _parser.skips("substitute") ) {
						Locale thesis_loc = _loc.branch();
						auto term = thesis_loc.cterm(_parser.get_term());
						_parser.skip(":=");
						CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
							return _loc.constant(x);
						}));
						CTerm t = obtain->ex.capp()->second;
// var'. (∀sym. props... ⟹ var') ⟹ var'
						t = t.weaken(thesis_loc).inst(var);
// (∀sym. props... ⟹ var) ⟹ var
						t = t.cbinary(IMP)->first;
// ∀sym. props... ⟹ var
						t = t.capp()->second.inst(term);
// props[sym:=term]... ⟹ var
						auto const& rule = Inference::rule(thesis_loc.assume("?thesis",t));
// assume this and prove var, i.e., prove props[sym:=term]...
						auto thesis = Inference(thesis_loc,var);// var ⟹ var
						thesis.apply(rule);// prop[sym:=term]... ⟹ var
						auto const& spec = Prover(*this,thesis_loc,{},thesis).deepen().proof_loop().intro();
// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
						intp.retain(_loc.cterm(term),spec);
					} else {
						if( !intp.retains() ) {
							throw Error("\"failed retain\"")(obtain->spec);
						}
					}
				} else {
					cout << "Complete!" << endl;
					_indent();
					_parser.skip("end");
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
	Opt<Thm> loop() {
		for(;;) try {
			if( _parser.skips("include") ) {
				load_locale(_parser.get_thm_name(),true);
				_parser.skip(";");
			} else if( _parser.skips("locale") ) {
				string name = _parser.get_token();
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
					string name = _parser.get_token();
					_parser.skip(";");
					auto loc = find_locale(name);
					cout << loc.pretty(*_syntax) << endl;
				}
			} else if( _parser.skips("in") ) {
				string name = _parser.get_token();
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
				auto const& thm = note();
				add_claim(cs,thm);
				if( cs.is_goal ) {
					print_goal();
				} else {
					cout << "note " << cs << _syntax->pretty_thm(thm) << endl;
				}
			} else if( _parser.skips("show") ) {
				auto cs = get_claim_status();
				cout << "Showing " << cs << flush;
				auto [prover,goal] = get_statement();
				add_claim(cs,prover.proof_loop().intro());
				if( _thesis ) {
					print_goal();
				} else {
					cout << "theory state" << endl;
				}
			} else if( _parser.skips("obtain") ) {
				string sym = _parser.get_token();
				_parser.skip("where");
				cout << "Obtaining " << sym << " where ";
				vector<string> names;
				vector<Term> props;
				get_named_terms([&]( Opt<string> const& s, Term const& t, bool ) {
					if( !s ) throw Error("missing name");
					names.push_back(*s);
					props.push_back(t);
					cout << s << ": " << _syntax->pretty_term(t) << ", ";
				});
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
				auto const& thm = prove(_loc,goal).proof_loop();
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
						add_claim( ClaimStatus(*name_it), prop );
						cout << *name_it << ": " << prop << endl << "\t";
						spec = ignore << spec;// ∀var. (props... ⟹ var) ⟹ var
						name_it++;
					} else {// spec: ∀var. (P ⟹ var) ⟹ var
						Thm prop = spec << refl;
						add_claim( ClaimStatus(*name_it), prop );
						cout << *name_it << ": " << prop << ';' << endl;
						break;
					}
				}
			} else if( _parser.skips("define") ) {
				Opt<string> name_op;
				if( _parser.skips("(") ) {
					name_op = _parser.get_token();
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
				if( _parser.skips("rewrite") ) {
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					_rewriter->register_refl(refl);
					_rewriter->register_imp(imp,true);
					_rewriter->register_imp(revimp,false);
					_rewriter->register_trans(trans);
					cout << "Registered rewriter: imp: " << _syntax->pretty_thm(imp) << ", rev: " <<  _syntax->pretty_thm(revimp) << ", refl: " << _syntax->pretty_thm(refl) << ", trans: " << _syntax->pretty_thm(trans) << endl;
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
					cout << "Registering congruence: ";
					while( auto const& thm = gets_thm() ) {
						_rewriter->register_cong(*thm);
						cout << _syntax->pretty_thm(*thm) << flush;
					};
					cout << endl;
				} else if( _parser.skips("define") ) {
					Thm const& beta = get_thm();
					cout << " beta: " << _syntax->pretty_thm(beta) << endl;
					_definer = OptRef<Definer>::make(_rewriter,beta);
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
			} else if( _parser.skips("end") || _parser.skips("") ) {
				return {};
			} else if( _thesis ) {
				if( _parser.skips("goal") ) {
					_parser.skip(";");
					print_goal();
				} else if( _parser.skips("apply") ) {
					int min, max;
					bool safe;
					if( _parser.skips("+") ) {
						min = 1; max = 255; safe = false;
					} else {
						min = max = 1; safe = true;
					}
					set<Inference::Rule> rules;
					while( auto const& thm = gets_thm() ) {
						rules.emplace(Inference::rule(*thm));
					}
					_parser.skip(";");
					_thesis->apply(rules,min,max,safe);
					print_goal();
				} else if( bool dir = false; _parser.skips("unfold") || ( dir = true, _parser.skips("fold") ) ) {
					bool discharge = _parser.skips("!");//TODO
					_rewrite(_loc,{},{0},1,discharge?255:0,!discharge,dir);
					_parser.skip(";");
					print_goal();
				} else if( _parser.skips("case") ) {
					auto goal = has_goal();
					if( !goal ) {
						throw Error("\"unexpected case\"");
					}
					auto subprf = Prover(*this,_loc.branch()).deepen();
					CTerm newgoal = goal->weaken(subprf._loc);
					cout << "Case ";
					if( _parser.skips("for") ) {// instantiate variables as long as names are given
						newgoal = strip_all(newgoal,subprf._loc,[&](string_view const& v)->Opt<string> {
							return gets_sym();
						});
						_parser.skips(",");
					}
					if( !_parser.skips(":=") ) {
						get_named_terms([&]( Opt<string> const& s, Term const& t, bool force ){
							auto imp = newgoal.cbinary(IMP);
							if( !imp ) {
								throw Error("case")(t);
							}
							newgoal = imp->second;
							if( imp->first != t ) {
								throw Error("case")(imp->first)(t);
							}
							CTerm ct = subprf._loc.enclose(t);
							Thm assm = s ? (cout << s), subprf._loc.assume(*s,ct) : subprf._loc.Ctxt::assume(ct);
							if( force ) {
								cout << "! ";
								subprf._forced_intros.insert(assm);
							} else {
								cout << ": ";
							}
							cout << _syntax->pretty_thm(assm) << ", " << flush;
						});
						if( _parser.skips("then") ) {
							if( _parser.get_term() != newgoal ) {
								throw Error("\"conclusion mismatch\"")(newgoal);
							}
						}
						_parser.skip(":=");
					}
					cout << "show " << _syntax->pretty_cterm(newgoal) << endl;
					subprf._thesis = Inference(subprf._loc,newgoal);
					_thesis->discharge(subprf._prompt().proof_loop());
					print_goal();
				} else if( _parser.skips("done") ) {
					_parser.skip(";");
					size_t fuel = 255;
					while( _thesis->goal_count() > 0 ) {
						_thesis->blast({},fuel);
					}
					auto ret = _thesis->concluding();
					if( !ret ) throw UnfinishedProof();
					return ret;
				} else if( _parser.skips("blast") ) {
					set<Inference::Rule> rules;
					while( auto const& thm = gets_thm() ) {
						rules.emplace(Inference::rule(*thm));
					}
					_parser.skip(";");
					size_t fuel = 255;
					_thesis->blast(rules,fuel);
					print_goal();
				} else if( _parser.skips("by") ) {
					set<Inference::Rule> rules;
					while( auto const& thm = gets_thm() ) {
						rules.emplace(Inference::rule(*thm));
					}
					_parser.skip(";");
					size_t fuel = 255;
					while( _thesis->goal_count() > 0 ) {
						_thesis->blast(rules,fuel);
					}
					return _thesis->concluding();
				} else if( _parser.skips("qed") ) {
					_parser.skip(";");
					auto ret = _thesis->concluding();
					if( !ret ) throw UnfinishedProof();
					return ret;
				} else if( _parser.skips("sorry") ) {
					_parser.skip(";");
					throw Error("sorry");
				} else {
					throw Error("unexpected")(_parser.get_token());
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
					string name = _parser.get_thm_name();
					_parser.skip(":");
					cout << "Assuming " << name << ": ";
					Locale var_loc = _loc.branch();
					for_variables(var_loc);
					Term assm = _parser.get_term();
					_loc.assume( name, var_loc.enclose(assm).lift(_loc.cterm(ALL)) );
					cout << _syntax->pretty_term(assm) << "; " << flush;
					_parser.skip(";");
					cout << endl;
				} else if( _parser.skips("import") ) {
					import(true);
				} else if( _parser.skips("finalize") ) {
					_parser.skip(";");
					_final = true;
					cout << "Finalized" << endl;
				} else {
					throw Error("unexpected")(_parser.get_token());
				}
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
	void load_locale( string_view const& name, bool open = false ) {
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
				if( open ) {
					auto prev_loc = _loc;
					_loc = _loc.branch(name);
					set_lexer(local_lexer);
					loop();
					set_lexer(prev);
					_loc = prev_loc;
				} else {
					Prover sub = Prover(*this,_loc.branch(name),{{dir,name}},{}).deepen();
					sub.set_lexer(local_lexer);
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

