#include<fstream>
#include<filesystem>
#include<ranges>
#include"inference.hpp"
#include"parser.hpp"
#include"definer.hpp"

#define FLAG_ERR (1 << 0)
#define FLAG_SYS (1 << 1)
#define FLAG_STA (1 << 2)
#define FLAG_CTXT (1 << 3)
#define FLAG_THY (1 << 4)
#define FLAG_MSG (1 << 5)
#define FLAG_PRF (1 << 6)

#define FLAGS_MIN (FLAG_SYS | FLAG_STA)
#define FLAGS_DEFAULT (FLAGS_MIN | FLAG_CTXT | FLAG_THY | FLAG_MSG)

#define ERR ( _out & FLAG_ERR )
#define SYS ( _out & FLAG_SYS )
#define STA ( _out & FLAG_STA )
#define CTXT ( _out & FLAG_CTXT )
#define THY ( _out & FLAG_THY )
#define MSG ( _out & FLAG_MSG )
#define PRF ( _out & FLAG_PRF )

using namespace std;

struct ClaimStatus {
	Opt<string> name;
	bool weak = false, intro = false, elim = false, cong = false, fallback = false, unfold = false, fold = false, inflated = false, followable = true;
	short after = 0;
	static ClaimStatus const INFLATED;
};
inline ClaimStatus const ClaimStatus::INFLATED =
	[](){ ClaimStatus ret; ret.intro = true; ret.inflated = true; return ret; }();

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.name ) {
		os << *cs.name;
	}
	if( cs.intro ) {
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

void init_lex( Lex& lex ) {
	lex.register_multi_op(int_of_chars("∀"));
	lex.register_multi_op(int_of_chars("⟹"));
	lex.register_single_op(',');
	lex.register_single_op(';');
	lex.register_multi_op(':');
	lex.register_multi_op('=');
	lex.register_multi_op('!');
	lex.register_multi_op('?');
	lex.register_multi_op('*');
	lex.register_multi_op('+');
	lex.register_multi_op('-');
	lex.register_multi_op('#');
	lex.register_multi_op('^');
}
void init_syntax( Syntax& syntax ) {
	syntax.infix(":",50,51,50);
	syntax.infix(",",-20,-19,-20);
	syntax.infix(";",-30,-29,-30);
	syntax.infix(":=",-1,-1,-2);
	syntax.prefix("if",-1,-2);
	syntax.infix("then",-2,-1,-2);
	syntax.infix("else",-2,-2,-1);
}

static Error const ProofMismatch = Error("#proof-mismatch");

class Prover : public Parser {
	Thy _thy;
	Lex& lex;
	bool _final = false;
	bool _through_error;
	unsigned char _depth;
	char _out;
	char _out_load;
	char _out_blast = 0;
	bool _no_syntax;
public:
	struct Error : ::Error {
		static inline Term const RT = Term("#prover");
		Error( Term const& msg ) : ::Error(RT(msg)) {
		}
	};
	static inline Error const THROUGH = Error("\"from here\"");
	Prover( Thy const& thy, istream& is, string_view const& filename, Lex& lex, bool through_error, char out, char out_load, unsigned char depth ) :
		_depth(depth),
		_thy(thy),
		lex(lex),
		Parser(is,filename,lex),
		_through_error(through_error),
		_out(out),
		_out_load(out_load) {
		if MSG cout << _indent();
	}
	Syntax const& syntax() const {
		return _thy.syntax();
	}
	Thy& thy() & {
		return _thy;
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
		if( !ret ) throw Error("\"expects a theorem\"");
		return *ret;
	}
	struct RewriteCtrl {
		size_t min;
		size_t max;
		vector<char> pos;
		bool normalize;
		Opt<string> rel;
	};
	RewriteCtrl _get_rewrite( Resolver& resolver, Thy& loc, bool rev ) {
		RewriteCtrl ret;
		auto const& rew = _thy.rewriter();
		if( !rew ) throw Error("\"rewriter not set\"");
		if( skips("(") ) {
			ret.rel = {get()};
			skip(")");
		}
		if( skips("[") ) {// parse position
			while( !skips("]") ) {
				ret.pos.push_back(get_int());
			}
		}
		if( skips("^") ) {
			ret.min = ret.max = get_nat(); ret.normalize = false;
		} else {
			ret.min = 1; ret.max = 255; ret.normalize = true;
		}
		while( auto const& arg = _gets_thm(loc) ) {
			auto rule = *arg;
			if( rev ) {
				rule = loc.dualize(rule,resolver);
			}
			loc.add_rewrite_rule(resolver.rules,rule,false);
		}
		return ret;
	}
	Opt<Thm> _gets_thm( Thy& loc ) {
		auto const& opt = gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = loc.thm(*opt);
		if( skips("[") ) {
			for(;;) {
				if( skips("of") ) {
					auto sub = loc.fork();
					auto tmp = ret.subst(sub);
					while( auto t = gets_term(1000) ) {
						tmp = tmp.instantiate(sub.ctxt().enclose(*t));
					}
					ret = tmp.intro();
				} else if( skips("OF") ) {
					auto sub = loc.branch();
					auto tmp = sub.weaken(ret);
					for(;;) {
						if( skips("_") ) {
							auto imp = tmp.cbinary(IMP);
							if( !imp ) throw Error("\"no premise for _\"");
							tmp = discharge(tmp,sub.assume(imp->first));
						} else if( auto const& arg = _gets_thm(sub) ) {
							tmp = discharge(tmp,*arg);
						} else if( skips("!") ) {
							auto imp = tmp.cbinary(IMP);
							if( !imp ) throw Error("\"no premise to blast\"");
							tmp = tmp.discharge(sub.prove(imp->first,_out_blast));
						} else {
							break;
						}
					}
					ret = tmp.intro();
				} else if( skips("THEN") ) {
					auto sub = loc.branch();
					auto tmp = sub.weaken(ret);
					auto thm = _get_thm(sub);
					auto sub2strip = sub.fork();
					auto [strip_thm,n] = strip_all(thm,sub2strip);
					auto strip_ctxt = strip_thm.ctxt();
					auto imp = strip_thm.cbinary(IMP);
					if( !imp ) throw Error("\"malformed THEN\"")(strip_thm);
					auto cond = imp->first;
					auto arg = tmp.subst(sub2strip);
					for(;;){
						arg = strip_all(arg,strip_ctxt.self()).first;
						auto imp = arg.cbinary(IMP);
						if( !imp ) break;
						arg = arg.discharge(strip_ctxt.assume(imp->first));
					}
					auto u = unify(arg,cond,[&](auto v){ return strip_ctxt.fixes(v); });
					if( !u ) throw Error("\"mismatching THEN\"")(arg)(strip_thm);
					auto strip2sub = Intp::make(strip_ctxt,sub);
					for(;;){
						if( auto const& v = strip2sub.fixing() ) {
							strip2sub.instantiate(sub.enclose( [&]()->Term{
								if( auto t = u->get(*v) ) return *t;
								return *v;
							}()));
						} else if( auto const& assm = strip2sub.assuming() ) {
							strip2sub.discharge(sub.assume(sub.cterm(*assm)));
						} else {
							break;
						}
					}
					thm = strip_thm.subst(strip2sub);
					ret = thm.discharge(arg.subst(strip2sub)).intro();
				} else if( skips("for") ) {
					while( auto x = gets(Lexer::Word) ) {
						loc.fix(*x);
					}
				} else if( bool dir = false; skips("unfolded") || (dir = true, skips("folded")) ) {
					auto inf = loc.resolver(_out_blast);
					auto ctrl = _get_rewrite(inf,loc,dir);
					ret = inf.rewrites(loc,ret,false);
				} else if( skips("dual") ) {
					auto resolver = Resolver(loc.rewriter(),_out_blast);
					ret = loc.dualize(ret,resolver);
				} else break;
				if( !skips(",") ) break;
			}
			skip("]");
		}
		return ret;
	}
	Thm _get_thm( Thy& loc ) {
		auto ret = _gets_thm(loc);
		if( !ret ) throw Error("\"expected a theorem\"")(get());
		return *ret;
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		while( auto const& name = gets_thm_name() ) {
			skip(":");
			Thm const& thm = get_thm();
			ret.insert({*name,thm});
		}
		return ret;
	}
	Opt<Term> gets_term_mod() {
		if( auto const& term = gets_term() ) {
			Term ret = *term;
			if( skips("$") ) {
				Subst subst = _thy.branch();
				do {
					string sym = get();
					skip(":=");
					subst.assign(sym,get_term_mod());
				} while( skips(",") );
				ret = ret.subst(subst);
			}
			return ret;
		}
		return {};
	}
	Term get_term_mod() {
		if( auto const& term = gets_term_mod() ) {
			return *term;
		}
		throw Error("\"expected a term\"")(get());
	}
	function<ostream&(ostream&)> _indent( char c = '>' ) const & {
		return [c,this]( ostream& os )->ostream& {
			for( int i = 0; i <= _depth; i++ ) {
				os << c;
			}
			return os << ' ' << flush;
		};
	}
	ClaimStatus get_claim_status( bool need_claim = true, bool allow_claim = true ) {
		ClaimStatus cs;
		cs.name = gets_thm_name();
		if( skips("!") ) {
			cs.intro = true;
			cs.inflated = true;
			return cs;
		} else if( skips("?") ) {
			cs.weak = true;
			cs.inflated = true;
			return cs;
		} else if( skips("(") ) {
			if( skips("weak") ) {
				cs.weak = true;
			} else if( skips("intro") ) {
				cs.intro = true;
			} else if( skips("cong") ) {
				cs.cong = true;
			} else if( skips("fallback") ) {
				cs.fallback = true;
			} else if( skips("elim") ) {
				cs.elim = true;
			} else if( skips("unfold") ) {
				cs.unfold = true;
			} else if( skips("fold") ) {
				cs.fold = true;
			} else {
				throw Error("\"unknown rule\"")(peek_token());
			}
			if( auto n = gets_nat() ) {
				cs.after = *n;
			}
			skip(")");
		} else if( need_claim ) {
			skip(":");
		} else if( allow_claim && skips(":") ) {
			cs.followable = false;
		} else {
		}
		return cs;
	}
	pair<ClaimStatus,Term> get_assm() {
		return {get_claim_status(),get_term()};
	}
	void add_claim( Thy& loc, ClaimStatus cs, Thm const& thm ) {
		if( cs.intro ) {
			if( cs.after > 0 ) {
				loc.add_thm(Thy::INF,thm,Elim::rule(thm,cs.after,'i'));
			} else {
				add_forced(loc,thm,true);
			}
		}
		if( cs.cong ) {
			_thy.register_cong(thm);
		}
		if( cs.fallback ) {
			_thy.register_fallback(thm);
		}
		if( cs.elim ) {
			loc.add_elim(thm);
		}
		if( cs.name ) {
			loc.add_thm(*cs.name,thm);
		}
		if( cs.unfold ) {
			if( cs.after > 0 ) {
				loc.add_thm(Thy::INF,thm,Elim::rule(thm,cs.after,'='));
			} else {
				auto [ind,rel,rule] = _thy.rewriter()->make_rule(thm,false);
				_thy.add_thm(Thy::REWRITE+rel,thm,rule);
			}
		}
		if( cs.fold ) {
			auto resolver = Resolver(loc.rewriter(),_out_blast);
			auto const& dual = _thy.dualize(thm,resolver);
			if( cs.after > 0 ) {
				loc.add_thm(Thy::INF,dual,Elim::rule(dual,cs.after,'='));
			} else {
				auto [ind,rel,rule] = _thy.rewriter()->make_rule(dual,false);
				_thy.add_thm(Thy::REWRITE+rel,dual,rule);
			}
		}
		if( cs.inflated ) {
			auto blaster = loc.resolver(_out_blast);
			blaster.inflate(loc,thm);
		}
	}
	void print_goal( Thesis const& thesis, string pre = "goals " ) {
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
	void _auto_instantiate( Import& intp, string const& sym, bool change ) {
		if( auto const& c = _thy.constant(sym) ) {
			intp.instantiate(*c);
		} else if( change ) {
			auto const& c = _thy.fix(sym);
			intp.instantiate(c);
			if CTXT {
				if( !MSG ) cout << _indent(' ');
				cout << "fixed " << _thy.pretty_sym(sym) << endl;
			}
		} else throw Error("\"auto instantiate failed\"")(sym);
	}
	void _auto_discharge( string const& prefix, Import& intp, pair<CTerm,string> const& assume, bool change, Resolver& infer ) {
		string assm_name = prefix;
		if( prefix != "" ) {
			assm_name += '.';
		}
		assm_name += assume.second;
		auto const& assm = assume.first;
		if( auto const& o = _thy.find_thm(assm_name,[&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto thm2 = thm.subst(import);
			if( thm2 == assm ) {
				intp.discharge(thm2);
				return {thm2};
			}
			return {};
		} ) ) {
			if MSG cout << "transferred " << assm_name << ": " << _thy.pretty(*o) << endl;
		} else if( change ) {
			Thm ret = _thy.add_assm(assm_name,assm);
			intp.discharge(ret);
			if CTXT {
				if( !MSG ) cout << _indent(' ');
				cout << "admitted " << assm_name << ": " << _thy.pretty(ret) << endl;
			}
		} else {
			if MSG cout << "blasting " << assm_name << ": " << _thy.pretty(assm) << endl;
			Thm ret = infer.prove(_thy,assm,true);
			intp.discharge(ret);
		}
	}
	void _auto_retain( Thy& org_thy, string const& prefix, Import& intp, tuple<string,Thm,CTerm,string> const& obtain, Resolver& infer ) {
		auto [sym,ex,spec,name] = obtain;
		if( auto csym = _thy.constant(sym) ) {
			CTerm const& stmt = spec.inst(*csym);
			if( !_thy.find_thm(name,[&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
				auto thm2 = thm.subst(import);
				if( stmt == thm2 ) {
					intp.retain(*csym,thm2);
					return {thm2};
				};
				return {};
			} ) ) {
			if MSG cout << "blasting " << name << ": " << _thy.pretty(stmt) << endl;
			Thm thm = infer.prove(_thy,stmt,true);
			intp.retain(*csym,thm);
			}
		} else {
			auto [sym_term,spec] = org_thy.obtain(sym,ex,name,false);
			intp.retain(sym_term,spec);
		}
	}
	void _update_parent( Thy& child ) {
		auto p = child.parent();
		if( !p ) return;
		auto resolver = Resolver({});
		while( auto obtain = p->obtaining() ) {
			auto const& [sym,ex,spec,name] = *obtain;
			auto [sym_term,thm] = child.obtain(sym,ex,name,false);
			p->retain(sym_term,thm);
		}
	}
	auto reader() const& {
		return [&]( Thy& thy, istream& fis, string_view const& filename ){
			if SYS {
				if( !MSG ) cout << _indent(' ');
				cout << "loading " << filename << endl;
			}
			Prover(thy,fis,filename,lex,true,_out_load,_out_load,_depth+1).loop();
			if ( SYS && _out_load & (FLAG_CTXT|FLAG_THY) ) {
				if( !MSG ) cout << _indent(' ');
				cout << "loaded " << filename << endl;
			}
		};
	}
	static void _print_prefix( string_view const& prefix ) {
		if( !prefix.empty() ) {
			cout << prefix << ": ";
		}
	}
	void import( bool change ) {
		string prefix;
		string name = get_thm_name();
		if( skips(":") ) {
			swap(prefix,name);
			name = get();
		}
		auto intp = _thy.thy(name,reader());
		auto src = intp.source();
		while( auto const& t = gets_term(1000) ) {
			auto const& fix = intp.fixing();
			if( !fix ) throw Error("\"unexpected instantiation\"")(*t);
			intp.instantiate(_thy.cterm(*t));
		}
		auto path = src.print_name();
		bool success = true;
		if( skips(";") ) {
			if MSG cout << (change ? "importing " : "interpreting ") << path << endl;
			_depth++;
			success = _import_loop(prefix,intp,change);
			_depth--;
		} else {
			skip(".");
			for(;;) {
				if( auto const& fix = intp.fixing() ) {
					_auto_instantiate(intp,*fix,change);
				} else if( auto const& assume = intp.assuming() ) {
					auto infer = _thy.resolver(_out_blast);
					_auto_discharge(prefix,intp,*assume,change,infer);
				} else if( auto const& obtain = intp.obtaining() ) {
					auto infer = _thy.resolver(_out_blast);
					_auto_retain(_thy,prefix,intp,*obtain,infer);
				} else {
					break;
				}
			}
			if( _no_syntax ) {
				_no_syntax = false;
				_thy.modify_syntax() = src.syntax();
			}
		}
		if( success ) {
			_update_parent(src);// in case of interpreting a child.
			if( prefix.empty() ) {
				if( src.rewriter() ) {
					_thy.import_rewrite(src,intp);
				}
				if( !_thy.definer() && src.definer() ) {
					_thy.setup_definer(src.definer()->beta().subst(intp));
				}
			}
			_thy.add_import(prefix,std::move(intp));
			if THY {
				if( !MSG ) cout << _indent(' ');
				if( change ) cout << "imported ";
				else cout << "interpreted ";
				_print_prefix(prefix);
				cout << path << endl;
			}
		}
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
			cout << pre << "retain ";
			if( auto const& o = obtain->spec_name ) {
				cout << *o << ": ";
			}
			cout << _thy.pretty(obtain->spec) << endl;
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
	bool _import_loop( string const& prefix, Import& intp, bool change ) {
		auto org_thy = _thy;
		_thy = org_thy.scope_temp("#import");// namespace
		for(;;) try {
			if MSG cout << _indent();
			if( _stats() ) {
			} else if( skips("note") ) {
				_note();
			} else if( skips("goal") ) {
				skip(".");
				_print_import_goal(intp,0,"\t");
			} else if( skips("goals") ) {
				skip(".");
				_print_import_goals(intp);
			} else if( skips("have") ) {
				_state();
			} else if( skips("interpret") ) {
				import(false);
			} else if( skips("instantiate") ) {
				vector<pair<string,Term>> map;
				for(;;) {
					auto x = get_sym();// the symbol to be instantiated
					map.emplace_back( x, skips(":=") ? get_term() : x );
					if( !skips(",") ) break;
				}
				skip(".");
				for( auto [x,t] : map ) {
					for(;;) {
						if( auto const& assume = intp.assuming() ) {
							auto infer = _thy.resolver(_out_blast);
							_auto_discharge(prefix,intp,*assume,change,infer);
						} else if( auto const& obtain = intp.obtaining() ) {
							auto infer = _thy.resolver(_out_blast);
							_auto_retain(org_thy,prefix,intp,*obtain,infer);
						} else if( auto const& fix = intp.fixing() ) {
							if( *fix == x ) break;
							_auto_instantiate(intp,*fix,change);
						} else {
							throw Error("\"unexpected instantiate\"")(x);
						}
					}
					intp.instantiate( change ? org_thy.cterm(t) : org_thy.enclose(t) );
					if MSG cout << "instantiated " << x << " := " << _thy.pretty(t) << endl;
				}
			} else if( skips("-") ) {
				auto pat = _get_subgoal();
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& obtain = intp.obtaining() ) {
						auto infer = _thy.resolver(_out_blast);
						_auto_retain(org_thy,prefix,intp,*obtain,infer);
					} else if( auto const& assume = intp.assuming() ) {
						auto [match,thm] = goal_matches(pat,assume->first);
						if( match ) {
							if( thm ) {
								intp.discharge(*thm);
								if MSG cout << "discharged " << assume->second << ": " << _thy.pretty(*thm) << endl;
							} else {
								if MSG cout << "aborted " << assume->second << ": " << _thy.pretty(assume->first) << endl;
							}
							break;
						} else {
							auto infer = _thy.resolver(_out_blast);
							_auto_discharge(prefix,intp,*assume,change,infer);
						}
					} else if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& obtain = intp.obtaining() ) {
						auto infer = _thy.resolver(_out_blast);
						_auto_retain(org_thy,prefix,intp,*obtain,infer);
					} else {
						break;
					}
				}
			} else if( skips("obtain") ) {
				_obtain(org_thy);
			} else if( skips("define") ) {
				_define(org_thy);
			} else if( skips("retain") ) {
				_retain(prefix,intp,change,org_thy);
			} else if( skips("oops") ) {
				return false;
			} else if( auto ctrl = gets_concluder() ) {
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& assume = intp.assuming() ) {
						_auto_discharge(prefix,intp,*assume,change,*ctrl);
					} else if( auto const& obtain = intp.obtaining() ) {
						_auto_retain(org_thy,prefix,intp,*obtain,*ctrl);
					} else {
						break;
					}
				}
				break;
			} else if( skips("") ) {
				cerr << location() << ": Unexpected EOF" << endl;
				exit(0);
			} else {
				throw Error("\"Unexpected\"")(get());
			}
		} catch( ::Error const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			if MSG cout << _indent();
		}
		_thy = org_thy;
		return true;
	}
	void _retain( string const& prefix, Import& intp, bool change, Thy& org_thy ) {
		auto sym = get_sym();// the symbol to be instantiated
		auto term = org_thy.cterm( skips(":=") ? get_term() : sym );
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change);
			} else if( auto const& assume = intp.assuming() ) {
				auto infer = _thy.resolver(_out_blast);
				_auto_discharge(prefix,intp,*assume,change,infer);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto const& [osym,ex,spec,spec_name] = *obtain;
				Thy thesis_loc = _thy.branch();
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
					auto thesis = Thesis::claim_exact(thesis_loc,var);// var ⟹ var
					thesis.apply(rule);// prop[sym:=term]... ⟹ var
					if( skips(";") ) {
						_depth++;
						if MSG {
							print_goal(thesis);
							_indent();
						}
						auto prf = _prove(thesis);
						_depth--;
						if( prf ) {
							auto const& spec = prf->intro();
							// ∀var. (props[sym:=term]... ⟹ var) ⟹ var
							intp.retain(term,spec);
						} else {
							if ERR cerr << "failed to retain " << _thy.pretty_sym(sym) << " " << _thy.pretty(t) << endl;
						}
					} else {
						skip(".");
						intp.retain(term,thesis.discharge_all().intro());
					}
					if MSG cout << "retained " << _thy.pretty_sym(sym) << " := " << _thy.pretty(term) << endl;
					break;
				}
				auto infer = _thy.resolver(_out_blast);
				_auto_retain(org_thy,prefix,intp,*obtain,infer);
			} else {
				throw Error("\"unexpected retain\"")(sym);
			}
		}
	}
	Intro make_rule( Thm const& thm ) {
		if( skips("!") ) {
			size_t n = get_nat();
			return Intro::imp(thm,n);
		} else if( skips("=") ) {
			return Intro::axiom(thm);
		} else {
			return Intro::rule(thm);
		}
	}
	Opt<Resolver> gets_concluder() {
		if( skips("by") ) {
			auto resolver = _thy.resolver(_out_blast);
			while( auto thm = gets_thm() ) {
				bool weak = skips("?");
				resolver.inflate(_thy,*thm);
				_thy.add_thm( weak ? Thy::WEAK : Thy::INTRO, *thm, make_rule(*thm) );
			}
			while( skips("#") ) {
				if( skips("elim") ) {
					while( auto elim = gets_thm() ) {
						_thy.add_elim(*elim);
					}
				} else if( int type = skips("unfold") ? 1 : skips("fold") ? 2 : skips("cong") ? 3 : 0 ) {
					auto const& rew = _thy.rewriter();
					if( !rew ) throw Error("\"rewriter not set\"");
					while( auto const& thm = _gets_thm(_thy) ) {
						auto rule = *thm;
						if( type == 2 ) {
							rule = _thy.dualize(rule,resolver);
						}
						if PRF {
							if( !MSG ) cout << _indent(' ');
							cout << "adding rewrite rule: " << _thy.pretty(rule) << endl;
						}
						_thy.add_rewrite_rule(resolver.rules,rule,type==3);
					}
				} else {
					throw Error("\"unexpected\"")(get());
				}
			}
			skip(".");
			return {resolver};
		} else if( skips(".") ) {
			return {_thy.resolver(_out_blast)};
		} else {
			return {};
		}
	}
	char get_print_level() {
		if( skips("none") ) return 0;
		if( skips("stat") ) return FLAG_STA;
		if( skips("system") ) return FLAG_STA | FLAG_SYS;
		if( skips("ctxt") ) return FLAG_STA | FLAG_SYS | FLAG_CTXT;
		if( skips("thy") ) return FLAG_STA | FLAG_SYS | FLAG_CTXT | FLAG_THY;
		if( skips("proof") ) return FLAG_STA | FLAG_SYS | FLAG_CTXT | FLAG_THY | FLAG_PRF;
		skips("default");
		return FLAGS_DEFAULT;
	}
	bool _stats() {
		if( skips("ctxt") ) {
			skip(".");
			cout << _thy.pretty_ctxt() << endl;
			return true;
		} else if( skips("thy") ) {
			if( skips(".") ) {
				cout << _thy << endl;
			} else {
				string name = get();
				skip(".");
				cout << _thy.thy(name,reader()).source() << endl;
			}
			return true;
		} else if( skips("thm") ) {
			string pref = "thm ";
			do {
				Thm thm = get_thm();
				cout << pref << _thy.pretty(thm) << endl;
				pref = "\t";
			} while( !skips(".") );
			return true;
		} else if( skips("thms") ) {
			bool shp = skips("#");
			string name = get_thm_name();
			string ref = shp ? "#"+name : name;
			cout << "thms " << ref << ":\n" << _thy.print_thms(ref);
			skip(".");
			return true;
		} else if( skips("term") ) {
			Term term = get_term();
			skip(".");
			cout << "term " << _thy.pretty(term) << endl;
			return true;
		} else if( skips("print") ) {
			if( skips("ctxt_id") ) {
				auto b = gets_bool().value_or(true);
				_thy.modify_syntax().print_ctxt(b);
				if MSG cout << "print ctxt_id" << endl;
			} else if( skips("load") ) {
				_out_load = get_print_level();
				if MSG cout << "print load level " << _out_load << endl;
			} else if( skips("prover") ) {
				_out_blast = gets_int().value_or(5);
				if MSG cout << "print prover level " << endl;
			} else {
				_out = get_print_level();
				if MSG cout << "print level " << _out << endl;
			}
			skip(".");
			return true;
		}
		return false;
	}
	void _note() {
		auto cs = get_claim_status();
		auto thm = get_thm();
		add_claim(_thy,cs,thm);
		if MSG cout << "note " << cs << _thy.pretty(thm) << endl;
		while( auto o = gets_thm() ) {
			add_claim(_thy,cs,*o);
			if MSG cout << "\t" << cs << _thy.pretty(*o) << endl;
		}
		skip(".");
	}
	Opt<Thm> _prove( Thesis& thesis ) {
		auto prev_thy = _thy;
		_thy = thesis.thy();
		auto ret = proof_loop(thesis);
		_thy = prev_thy;
		return ret;
	}
	Opt<pair<ClaimStatus,Thm>> _state() {
		auto cs = get_claim_status();
		if MSG cout << "showing " << cs << flush;
		auto assm_thy = _thy.branch();
		bool vars;
		for(;;) {
			if( skips("for") ) {
				vars = true;
				if MSG cout << "for" << flush;
				while( auto const& sym = gets_sym() ) {
					if MSG cout << ' ' << *sym << flush;
					assm_thy.fix(*sym);
				}
				skips(",");
			} else if( skips("if") ) {
				if MSG {
					if( vars ) {
						cout << ' ';
					}
					cout << "if " << flush;
				}
				for(;;) {
					if( skips("[") ) {
						if MSG cout << "[ ";
						for(;;) {
							auto t = get_term();
							if MSG cout << _thy.pretty(t);
							add_claim(assm_thy,ClaimStatus::INFLATED,assm_thy.assume(t));
							if( !skips(",") ) break;
							if MSG cout << ", " << flush;
						}
						skip("]");
						if MSG cout << " ] ";
					} else {
						auto cs = get_claim_status();
						auto t = get_term();
						if MSG cout << cs << _thy.pretty(t) << ", " << flush;
						add_claim(assm_thy,cs,assm_thy.assume(t));
					}
					if( !skips(",") ) break;
				};
				skip("then");
				if MSG cout << "then ";
			} else {
				break;
			}
		}
		Term t = get_term(0);
		CTerm goal = assm_thy.enclose(t);
		if MSG cout << _thy.pretty(goal) << endl;
		if( skips(";") ) {
			auto thesis = Thesis::claim_exact(assm_thy,goal);
			_depth++;
			if MSG cout << _indent();
			auto o = _prove(thesis);
			_depth--;
			if( o ) {
				auto thm = o->intro();
				add_claim(_thy,cs,thm);
				return {{cs,thm}};
			} else {
				if ERR cerr << "failed to prove " << cs << thesis.goal();
				return {};
			}
		}
		skip(".");
		auto thm = assm_thy.prove(goal).intro();
		add_claim(_thy,cs,thm);
		return {{cs,thm}};
	}
	void _define( Thy& org_thy ) {
		Opt<string> name_op;
		if( skips("[") ) {
			name_op = get();
			skip("]");
		}
		Term l = get_term();
		skip(":=");
		Term r = get_term();
		skip(".");
		auto [f,spec] = org_thy.define(l,r,name_op);
		Thm def = spec << _thy.thm("imp.refl");
		string name = (name_op ? *name_op : f) + "_def";
		_thy.add_thm(name,def);
		if MSG cout << "defined " << name << ": " << _thy.pretty(l) << " := " << _thy.pretty(r) << endl;
	}
	void local_thy( Thy& loc, bool finalized ) {
		_depth++;
		if MSG cout << _indent();
		swap(_thy,loc);
		swap(_final,finalized);
		loop();
		swap(_thy,loc);
		swap(_final,finalized);
		_depth--;
	}
	bool _proof_follows() {
		if( skips(";") ) {
			return true;
		} else {
			skip(".");
			return false;
		}
	}
	struct GoalPat {
		ClaimStatus cs;
		vector<Sum<string,pair<ClaimStatus,Opt<Term>>>> decls;
		Opt<Term> concl;
		bool proof;
	};
	GoalPat _get_subgoal() {
		auto ret = GoalPat();
		for(;;) {
			if( skips("for") ) {
				while( auto o = gets_sym() ) {
					ret.decls.emplace_back(*o);
				}
				if( skips(",") ) {
					ret.concl = {get_term()};
					ret.proof = _proof_follows();
					return ret;
				}
				continue;
			}
			if( skips("if") ) {
				do {
					auto const& cs = get_claim_status(false);
					auto const& assm = gets_term();
					ret.decls.emplace_back(pair<ClaimStatus,Opt<Term>>{cs,assm});
				} while( skips(",") );
				if( skips("then") ) continue;
			}
			break;
		}
		if( auto const& concl = gets_term() ) {
			ret.concl = {concl};
			ret.proof = _proof_follows();
			return ret;
		}
		ret.proof = _proof_follows();
		return ret;
	}
	/** @return first whether the goal pattern matches, and then the theorem if the proof was not aborted. */
	pair<bool,Opt<Thm>> goal_matches( GoalPat const& pat, CTerm const& goal ) {
		auto loc = _thy.branch();
		auto to_loc = *loc.parent();
		auto loc_goal = goal.subst(to_loc);
		auto css = vector<ClaimStatus>();
		for( auto const& decl : pat.decls ) {
			if( auto const& var = decl.ref<0>() ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) return {false,{}};
				loc_goal = all->inst(loc.fix(*var));
			} else if( auto const& p = decl.ref<1>() ) {
				auto const& [cs,stmt] = *p;
				if( stmt ) {
					size_t prev = loc.revision();
					auto assm = loc.assume(*stmt);
					while( auto const& v = loc.fixed(prev) ) {
						auto all = loc_goal.cunary(ALL);
						if( !all || !all->bind() ) return {false,{}};
						loc_goal = all->inst(loc.cterm(*v));
						prev++;
					}
					auto imp = loc_goal.cbinary(IMP);
					if( !imp || *stmt != imp->first ) return {false,{}};
					add_claim(loc,cs,assm);
					loc_goal = imp->second;
				} else {
					auto imp = loc_goal.cbinary(IMP);
					if( !imp ) return {false,{}};
					auto assm = loc.assume(imp->first);
					add_claim(loc,cs,assm);
					loc_goal = imp->second;
				}
				css.push_back(cs);
			} else {
				assert(false);
			}
		}
		if( pat.concl ) {
			size_t prev = loc.revision();
			auto concl = loc.enclose(*pat.concl);
			while( auto const& v = loc.fixed(prev) ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) return {false,{}};
				loc_goal = all->inst(loc.cterm(*v));
				prev++;
			}
			if( loc_goal != concl ) return {false,{}};
		}
		if( pat.proof ) {
			if MSG {
				auto csi = css.begin();
				for( size_t i = 0; i < loc.revision(); ) {
					if( auto const& v = loc.fixed(i) ) {
						cout << "for " << _thy.pretty(*v) << ' ';
						for(;;) {
							i++;
							auto const& v = loc.fixed(i);
							if(!v) break;
							cout << _thy.pretty(*v) << ' ';
						}
						continue;
					}
					if( auto const& assm = loc.assumed(i) ) {
						cout << "if " << *csi << _thy.pretty(*assm);
						for(;;) {
							i++;
							csi++;
							auto const assm = loc.assumed(i);
							if( !assm ) break;
							cout << ", " << *csi << _thy.pretty(*assm);
						}
						cout << ' ';
						continue;
					}
					assert(false);
				}
				cout << "show " << _thy.pretty(loc_goal) << endl;
			}
			auto thesis = Thesis::claim_exact(loc,loc_goal);
			_depth++;
			if MSG cout << _indent();
			auto thm = _prove(thesis);
			_depth--;
			if( !thm ) return {true,{}};
			Thm ret = thm->intro();
			add_claim(_thy,pat.cs,ret);
			return {true,{ret}};
		}
		auto infer = loc.resolver(_out_blast);
		Thm ret = infer.prove(loc,loc_goal,true).intro();
		add_claim(_thy,pat.cs,ret);
		return {true,{ret}};
	}
	bool _thy_decl() {
		if( skips("theory") ) {
			string name = get(Lexer::Word);
			auto loc = _thy.branch(name,"");
			while( auto sym = gets_sym() ) {
				loc.fix(*sym);
			}
			if( skips(":") ) {
				if THY {
					if( !MSG ) cout << _indent(' ');
					cout << "creating theory " << name << endl;
				}
				local_thy(loc,false);
				_thy.add_thy(loc);
				if MSG cout << "created theory " << name << endl;
			}
		} else if( skips("namespace") ) {
			auto name = get(Lexer::Word);
			skip(":");
			if THY {
				if( !MSG ) cout << _indent(' ');
				cout << "creating namespace " << name << endl;
			}
			auto loc = _thy.scope(name);
			local_thy(loc,_final);
			_thy.add_thy(loc);
			if MSG cout << "created namespace " << name << endl;
		} else if( skips("context") ) {
			string name = get();
			skip("begin");
			auto loc = _thy.thy(name,reader()).source();
			if THY {
				if( !MSG ) cout << _indent(' ');
				cout << "in context " << name << endl;
			}
			loc.reset_rewrite();
			local_thy(loc,true);
			if MSG cout << "left " << name << endl;
		} else if ( skips("lemma") || skips("theorem") || skips("proposition") ) {
			auto o = _state();
			if MSG if( o ) {
				auto const& [cs,thm] = *o;
				cout << "proved " << cs << _thy.pretty(thm) << endl;
			}
		} else if( skips("note") ) {
			_note();
		} else {
			return false;
		}
		return true;
	}
	bool _shared_decl() {
		if( skips("obtain") ) {
			_obtain(_thy);
		} else if( skips("define") ) {
			_define(_thy);
		} else if( skips("interpret") ) {
			import(false);
		} else {
			return false;
		}
		return true;
	}
	Opt<Thm> proof_loop( Thesis& thesis ) {
		for(;;) try {
			if( _stats() || _shared_decl() ) {
			} else if( skips("note") ) {
				_note();
			} else if( skips("goal") ) {
				skip(".");
				if STA print_goal(thesis);
			} else if( skips("have") ) {
				_state();
				if MSG print_goal(thesis);
			} else if( skips("show") ) {
				if( auto o = _state() ) {
					auto [cs,thm] = *o;
					for(;;) {
						auto goal = thesis.has_goal();
						if( !goal ) throw Error("\"no goal to matches\"")(thm);
						if( *goal == thm ) break;
						thesis.auto_discharge();
					}
					thesis.discharge(thm);
				}
			} else if( skips("apply") ) {
				int min, max;
				bool safe, wide;
				if( skips("+") ) {
					max = 255; safe = false; wide = true;
				} else {
					max = 0; safe = true; wide = false;
				}
				auto rules = set<Intro>();
				while( auto thm = gets_thm() ) {
					rules.emplace(make_rule(*thm));
				}
				min = rules.size();
				if( max == 0 ) max = min;
				bool more = _proof_follows();
				thesis.apply(rules,min,max,safe,wide);
				if( !more ) return thesis.discharge_all();
				if MSG print_goal(thesis,"applied goals:\n\t");
			} else if( bool dir = false; skips("unfold") || ( dir = true, skips("fold") ) ) {
				auto inf = _thy.resolver(_out_blast);
				auto ctrl = _get_rewrite(inf,_thy,dir);
				bool more = _proof_follows();
				inf.rewrites(thesis,false,ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos,ctrl.rel);
				if( !more ) return thesis.discharge_all();
				if MSG print_goal( thesis, dir ? "folded goal " : "unfolded goal " );
			} else if( skips("-") ) {
				auto pat = _get_subgoal();
				for(;;) {
					auto goal = thesis.has_goal();
					if( !goal ) throw Error("\"unexpected subgoal\"");
					auto [match,thm] = goal_matches(pat,*goal);
					if( match ) {
				 		if( thm ) {
							thesis.discharge(*thm);
						} else {
							if MSG cout << "proof aborted: " << _thy.pretty(*goal) << endl;
						}
						break;
					} else {
						thesis.auto_discharge();
					}
				}
				if MSG print_goal(thesis,"next goals ");
			} else if( auto infer = gets_concluder() ) {
				return infer->discharge_all(thesis);
			} else if( skips("oops") ) {
				return {};
			} else if( skips("") ) {
				cerr << location() << ": Unexpected EOF" << endl;
				exit(0);
			} else {
				throw Error("\"unexpected\"")(get());
			}
			if MSG cout << _indent();
		} catch ( ::Error const& e ) {
			if( _through_error ) throw e;
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if MSG cout << _indent();
		}
	}
	function<Term(Parser&)> _collect_handler( Term collect ) const& {
		return [=,this]( Parser& parser ) {
			return collect(parser.get_term(-1));
		};
	}
	void loop() {
		for(;;) try {
			if( _stats() || _thy_decl() || _shared_decl() ) {
			} else if( skips("set") ) {
				if( skips("rewrite") ) {
					bool def = skips("!") || !_thy.rewriter();
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					if MSG cout << "registering rewriter:\n\timp: " << _thy.pretty(imp) <<
						"\n\trev: " <<  _thy.pretty(revimp) <<
						"\n\trefl: " << _thy.pretty(refl) <<
						"\n\ttrans: " << _thy.pretty(trans);
					_thy.register_refl(refl,def);
					_thy.register_imp(imp,true);
					_thy.register_imp(revimp,false);
					_thy.register_trans(trans);
					if MSG cout << endl;
				} else if( skips("trans") ) {
					if MSG cout << "registering transitivity: ";
					while( auto const& thm = gets_thm() ) {
						_thy.register_trans(*thm);
						if MSG cout << _thy.pretty(*thm);
					}
					if MSG cout << endl;
				} else if( skips("dual") ) {
					if MSG cout << "registering dual: ";
					while( auto const& thm = gets_thm() ) {
						_thy.register_dual(*thm);
						if MSG cout << _thy.pretty(*thm);
					};
					if MSG cout << endl;
				} else if( skips("to_true") ) {
					auto thm = get_thm();
					if MSG cout << "registering to_true: " << _thy.pretty(thm) << endl;
					_thy.register_to_true(thm);
				} else if( skips("define") ) {
					Thm const& beta = get_thm();
					if MSG cout << " beta: " << _thy.pretty(beta) << endl;
					_thy.setup_definer(beta);
				} else if( skips("compr") ) {
					auto opener = get();
					if( skips("_") ) {
						if( skips(".") ) {
							skip("_");
							auto closer = get();
							skip(":=");
							auto actual = get_sym();
							_thy.modify_syntax().compr(opener,closer,actual);
							if MSG cout << "comprehension: " << opener << "_. _" << closer << " := " << _thy.pretty(actual) << endl;
						} else {
							auto next = get();
							if( skips("_") ) {
								skip(".");
								skip("_");
								auto closer = get();
								skip(":=");
								auto actual = get_sym();
								_thy.modify_syntax().bcompr(opener,next,closer,actual);
								if MSG cout << "bounded comprehension: " << opener << "_ " << next << "_. _" << closer << " := " << _thy.pretty(actual) << endl;
							} else {
								skip(":=");
								auto actual = get_sym();
								_thy.modify_syntax().singleton_compr(opener,next,actual);
								if MSG cout << "singleton comprehension: " << opener << "_ " << next << " := " << _thy.pretty(actual) << endl;
							}
						}
					} else {
						auto closer = get();
						skip(":=");
						auto actual = get_sym();
						_thy.modify_syntax().empty_compr(opener,closer,actual);
						if MSG cout << "empty comprehension: " << opener << ' ' << closer << " := " << _thy.pretty(actual) << endl;
					}
				}
				skip(".");
			} else if( skips("symbol") ) {
				bool solo = skips("solo");
				if MSG cout << "registering symbols";
				while( !skips(".") ) {
					string const& sym = get();
					int ch = int_of_chars(sym.data());
					if( solo ) {
						lex.register_single_op(ch);
					} else {
						lex.register_multi_op(ch);
					}
					if MSG cout << ' ' << sym;
				}
				if MSG cout << endl;
			} else if( skips("prefix") ) {
				string sym = get();
				int rlevel = get_int();
				int level = get_int();
				_make_own_parser();
				_thy.modify_syntax().prefix(sym,level,rlevel);
				if MSG cout << "new prefix operator " << sym << endl;
				skip(".");
			} else if( skips("infix") ) {
				string sym = get();
				int llevel = get_int();
				int rlevel = get_int();
				int level = get_int();
				_make_own_parser();
				_thy.modify_syntax().infix(sym,level,llevel,rlevel);
				if MSG cout << "new infix operator " << sym << endl;
				skip(".");
			} else if( skips("binder") ) {
				string sym = get();
				int llevel = get_int();
				int rlevel = get_int();
				_make_own_parser();
				_thy.modify_syntax().binder(sym,llevel,rlevel);
				if MSG cout << "new binder " << sym << endl;
				skip(".");
			} else if( skips("binder_middle") ) {
				string prefix = get();
				string mid = get();
				string sym = get();
				_make_own_parser();
				_thy.modify_syntax().binder_mid(prefix,mid,sym);
				if MSG cout << "new binder middle " << prefix << " x " << mid << " y. z := " << sym << " y (x. z)" << endl;
				skip(".");
			} else if( skips("end") || skips("") ) {
				return;
			} else if( !_final ) {
				if( skips("fix") ) {
					if CTXT {
						if(!MSG) cout << _indent(' ');
						cout << "fixing";
					}
					for(;;) {
						if ( auto sym = gets_sym() ) {
							_thy.fix(*sym);
							if CTXT cout << ' ' << _thy.syntax().pretty_sym(*sym) << flush;
						} else {
							break;
						}
					}
					if CTXT cout << '.' << endl;
					skip(".");
				} else if( skips("assume") ) {
					auto cs = get_claim_status();
					Ctxt assm_loc = _thy.Ctxt::fork().ctxt();
					for(;;) {
						if( skips("for") ) {
							while( auto const& sym = gets_sym() ) {
								assm_loc.fix(*sym);
							}
							skips(",");
						} else if( skips("if") ) {
							do {
								assm_loc.assume(get_term());
							} while( skips(",") );
							skip("then");
						} else {
							break;
						}
					}
					auto assm = assm_loc.enclose(get_term()).intro();
					Thm thm = cs.name ? _thy.add_assm(*cs.name,assm) : _thy.assume(assm);
					add_claim(_thy,cs,thm);
					if CTXT {
						if( !MSG ) cout << _indent(' ');
						cout << "assumed " << cs << _thy.pretty(assm) << ". " << endl;
					}
					skip(".");
				} else if( skips("import") ) {
					import(true);
				} else if( skips("begin") ) {
					_final = true;
					if MSG cout << "finalized" << endl;
				} else {
					throw Error("\"unexpected\"")(get());
				}
			} else {
				throw Error("\"unexpected\"")(get());
			}
			if MSG cout << _indent();
		} catch ( ::Error const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			if MSG cout << _indent();
		}
	}
	void _obtain( Thy& org_thy ) {
		string sym = get_sym();
		vector<CTerm> props;
		vector<pair<ClaimStatus,Thm>> prop_thms;
		Thy thesis_thy = _thy.branch();
		CTerm var = thesis_thy.fix("_thesis");
		Thy goal_thy = thesis_thy.branch();
		goal_thy.fix(sym);
		auto props_thy = org_thy.branch();
		props_thy.fix(sym);
		if MSG cout << "obtaining " << sym;
		if( skips("where") ) {
			if MSG cout << " where" << endl;
			for(;;) {
				auto [cs,t] = get_assm();
				Thm thm = props_thy.assume(props_thy.fork().ctxt().enclose(t).intro());
				add_claim(props_thy,cs,thm);
				prop_thms.emplace_back(cs,thm);
				props.push_back(goal_thy.fork().ctxt().enclose(t).intro());
				if MSG cout << '\t' << cs << _thy.pretty(thm) << endl;
				if( !skips(",") ) break;
			}
		}
		CTerm goal = goal_thy.weaken(var);
		for( auto& prop : ranges::reverse_view(props) ) {
			goal = prop >>= goal;
		}
		goal = goal.lift(thesis_thy.cterm(ALL)) >>= var;
		goal = goal.lift(_thy.cterm(ALL));
		auto thesis = Thesis::claim_exact(_thy,goal);
		_depth++;
		skip(";");
		if MSG cout << _indent();
		auto const& thm = _prove(thesis);
		_depth--;
		if( thm ) {
			auto [sym_term,deriver] = org_thy.obtain(sym,*thm,make_spec_name(string(sym)),true);
			// deriver: ∀thesis. (p ⟹ ... ⟹ thesis) ⟹ thesis
			for( auto const& [cs,prop_thm] : prop_thms ) {
				auto const& arg = prop_thm.intro();// props... ⟹ prop_i
				Thm prop = deriver << arg;// prop_i
				add_claim(_thy,cs,prop);
			}
			if MSG cout << "obtained " << sym << endl;
		} else {
			if ERR cout << "failed to obtain " << sym << endl;
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

void run( istream& is, string_view const& name, bool exit_on_error, char out ) {
	auto root = Thy("Root","Root");// the empty root theory, linked to the "Root" directory
	auto lex = Lex();
	init_lex(lex);
	init_syntax(root.modify_syntax());
	Thy thy = root.branch(name,"");
	auto prover = Prover(thy,is,name,lex,exit_on_error,out,FLAG_SYS,0);
	try {
		prover.loop();
	} catch( Error const& e ) {
		exit(-1);
	}
}

int main(int argc, char* argv[]) {
	bool exit_on_error = false;
	if( argc == 1 ) {
		run(cin,"#stdin",false,FLAGS_DEFAULT);
	} else {
		string name = argv[1];
		auto fin = fstream(name);
		run(fin,name,true,FLAGS_DEFAULT);
	}
	cout << "bye!" << endl;
	return 0;
}

