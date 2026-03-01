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

string const RULIFY = "#rulify";
string const RULIFY_CONG = "#rcong";

struct ClaimStatus {
	bool weak = false, intro = false, elim = false, dual = false, cong = false, fallback = false, unfold = false, fold = false, inflated = false, rulify = false, rulify_cong = false, followable = true;
	unsigned char after = 0;
	unsigned char prems = 255;
	bool strip_all = true;
	static ClaimStatus const INFLATED;
};
inline ClaimStatus const ClaimStatus::INFLATED =
	[](){ ClaimStatus ret; ret.intro = true; ret.inflated = true; return ret; }();

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.intro ) {
		os << "(intro";
		if( cs.after > 0 ) {
			os << " after " << (int)cs.after;
		}
		if( cs.prems != 255 ) {
			os << ' ' << (int)cs.prems;
		}
		os << ')';
	}
	if( cs.weak ) {
		os << "(weak)";
	}
	if( cs.elim ) {
		os << "(elim)";
	}
	if( cs.dual ) {
		os << "(dual)";
	}
	if( cs.unfold ) {
		os << "(unfold)";
	}
	if( cs.fold ) {
		os << "(fold)";
	}
	if( cs.cong ) {
		os << "(cong)";
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
	lex.register_multi_op('<');
	lex.register_multi_op('=');
	lex.register_multi_op('>');
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
	syntax.prefix("for",-1,-1);
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
	char _out_resolver = 0;
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
		size_t rep = 0;
		if( skips("[") ) {
			do {
				if( skips("at") ) {// parse position
					while( auto i = gets_int() ) {
						ret.pos.push_back(*i);
					}
				} else if( skips("on") ) {
					ret.rel = {get_sym()};
				} else if( skips("repeat") ) {
					rep = get_nat();
				} else {
					break;
				}
			} while( skips(",") );
			skip("]");
		}
		ret.min = 1;
		ret.max = 0;
		ret.normalize = skips("+");
		while( auto const& arg = _gets_thm(loc) ) {
			auto rule = *arg;
			if( rev ) {
				rule = loc.dualize(rule,resolver);
			}
			resolver.rew->add_rewrite_rule(resolver.rules,rule,false);
			ret.max++;
		}
		if( rep > 0 ) {
			ret.min = ret.max = rep;
		} else if( ret.normalize ) {
			ret.max = 255;
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
						tmp = tmp.allE(sub.ctxt().enclose(*t));
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
							tmp = tmp.impE(sub.prove(imp->first,_out_resolver));
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
						arg = arg.impE(strip_ctxt.assume(imp->first));
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
					ret = thm.impE(arg.subst(strip2sub)).intro();
				} else if( skips("for") ) {
					while( auto x = gets(Lexer::Word) ) {
						loc.fix(*x);
					}
				} else if( int mode = skips("unfold") ? 1 : skips("fold") ? 2 : 0 ) {
					auto resolver = loc.resolver(_out_resolver);
					auto ctrl = _get_rewrite(resolver,loc,mode==2);
					ret = resolver.rewrites(loc,ret,{},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos);
				} else if( skips("simp") ) {
					auto const& rew = loc.rewriter(SIMP);
					auto resolver = Resolver(rew,_out_resolver);
					while( auto thm = gets_thm() ) {
						rew.add_rewrite_rule(resolver.rules,*thm,false);
					}
					ret = resolver.rewrites(loc,ret,{SIMP},1,255,true,{});
				} else if( skips("rule") ) {
					auto const& rew = loc.rewriter(RULIFY);
					auto resolver = Resolver(rew,_out_resolver);
					ret = resolver.rewrites(loc,ret,{RULIFY},1,255,true,{});
				} else if( skips("dual") ) {
					auto resolver = Resolver({},_out_resolver);
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
	Opt<ClaimStatus> gets_claim_status( bool need_claim = true, bool allow_claim = true ) {
		ClaimStatus cs;
		if( skips("!") ) {
			cs.intro = true;
			cs.inflated = true;
		} else if( skips("?") ) {
			cs.weak = true;
			cs.inflated = true;
		} else if( skips("(") ) {
			do {
				if( skips("weak") ) {
					cs.weak = true;
					if( skips("after") ) {
						cs.after = get_int();
					}
				} else if( skips("intro") ) {
					cs.intro = true;
					if( skips("after") ) {
						cs.after = get_int();
					} else if( auto n = gets_int() ) {
						cs.prems = *n;
					}
					if( skips("=") ) {
						cs.strip_all = false;
					}
				} else if( skips("cong") ) {
					cs.cong = true;
				} else if( skips("fallback") ) {
					cs.fallback = true;
				} else if( skips("rule" ) ) {
					cs.rulify = true;
				} else if( skips("rule_cong") ) {
					cs.rulify_cong = true;
				} else if( skips("elim") ) {
					cs.elim = true;
				} else if( skips("dual") ) {
					cs.dual = true;
				} else if( skips("simp") ) {
					cs.unfold = true;
					if( skips("after") ) {
						cs.after = get_int();
					}
				} else if( skips("fold") ) {
					cs.fold = true;
				} else {
					throw Error("\"unknown rule\"")(peek_token());
				}
			} while( skips(",") );
			skip(")");
		} else {
			return {};
		}
		return {cs};
	}
	void add_claim( Thy& loc, Opt<string> const& name, Opt<ClaimStatus> const& cs, Thm const& thm ) {
		ThmInfo info = {};
		if( cs ) {
			if( cs->inflated ) {
				auto blaster = loc.resolver(_out_resolver);
				blaster.inflate(loc,thm);
			}
			if( cs->intro ) {
				if( cs->after > 0 ) {
					info = {Elim::rule(thm,cs->after-1,'!')};
					loc.add_thm(INF,thm,info);
				} else {
					info = {Intro::imp(thm,cs->prems,cs->strip_all)};
					add_intro(loc,thm,*info.ref<Intro>(),true);
				}
			}
			if( cs->weak ) {
				if( cs->after > 0 ) {
					info = {Elim::rule(thm,cs->after-1,'?')};
					loc.add_thm(INF,thm,info);
				} else {
					info = {Intro::imp(thm,cs->prems,cs->strip_all)};
					add_intro(loc,thm,*info.ref<Intro>(),false);
				}
			}
			if( cs->cong ) {
				loc.modify_rewriter(SIMP).register_cong(thm);
			}
			if( cs->fallback ) {
				loc.modify_rewriter(SIMP).register_fallback(thm);
			}
			if( cs->rulify ) {
				auto [ind,rel,rule] = loc.rewriter(RULIFY).make_rule(thm,false);
				info = {rule};
				loc.add_thm(RULIFY+rel,thm,info);
			}
			if( cs->rulify_cong ) {
				loc.modify_rewriter(RULIFY).register_cong(thm);
			}
			if( cs->elim ) {
				info = {Elim::rule(thm,0,'?')};
				loc.add_thm(ELIM,thm,info);
			}
			if( cs->dual ) {
				loc.register_dual(thm);
			}
			if( cs->unfold ) {
				if( cs->after > 0 ) {
					info = {Elim::rule(thm,cs->after-1,'=')};
					loc.add_thm(INF,thm,info);
				} else {
					auto [ind,rel,rule] = loc.rewriter(SIMP).make_rule(thm,false);
					info = {rule};
					loc.add_thm(SIMP+rel,thm,info);
				}
			}
			if( cs->fold ) {
				auto resolver = Resolver({},_out_resolver);
				auto const& dual = loc.dualize(thm,resolver);
				if( cs->after > 0 ) {
					loc.add_thm(INF,dual,Elim::rule(dual,cs->after,'='));
				} else {
					auto [ind,rel,rule] = loc.rewriter(SIMP).make_rule(dual,false);
					loc.add_thm(SIMP+rel,dual,rule);
				}
			}
		}
		if( name ) {
			loc.add_thm(*name,thm,info);
		}
	}
	void print_goals( Thesis const& thesis, string pre = "goals:\n\t" ) {
		Term acc = thesis.thm();
		size_t i = 0;
		while( i < thesis.goal_count() ) {
			auto const& imp = acc.binary(IMP);
			i++;
			cout << pre << i << ". " << _thy.pretty(imp->first) << endl;
			acc = imp->second;
			pre = "\t";
		}
		if( i == 0 ) {
			cout << "no goal" << endl;
		}
	}
	void print_goal( Thesis const& thesis, string_view const& pre ) {
		if( auto goal = thesis.has_goal() ) {
			cout << pre << _thy.pretty(*goal) << endl;
		} else {
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
	void _auto_discharge( Thy& org_thy, string const& prefix, Import& intp, pair<CTerm,string> const& assume, bool change, Resolver& infer, bool unprefixed ) {
		auto const& assm = assume.first;
		auto f = [&]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto thm2 = thm.subst(import);
			if( thm2 == assm ) {
				intp.discharge(thm2);
				return {thm2};
			}
			return {};
		};
		auto assm_name = assume.second;
		if( auto const& o = _thy.find_thm(assm_name,f) ) {
			if MSG cout << "transferred " << assm_name << ": " << _thy.pretty(*o) << endl;
			return;
		}
		if( !unprefixed ) {
			assm_name = prefix+'.'+assm_name;
			if( auto const& o = _thy.find_thm(assm_name,f) ) {
				if MSG cout << "transferred " << assm_name << ": " << _thy.pretty(*o) << endl;
				return;
			}
		}
		if( change ) {
			Thm ret = org_thy.add_assm(assm_name,assm);
			intp.discharge(ret);
			if CTXT {
				if( !MSG ) cout << _indent(' ');
				cout << "admitted " << assm_name << ": " << _thy.pretty(ret) << endl;
			}
			return;
		}
		if MSG cout << "blasting " << assm_name << ": " << _thy.pretty(assm) << endl;
		Thm ret = infer.prove(_thy,assm,{SIMP});
		intp.discharge(ret);
	}
	void _auto_retain( Thy& org_thy, string const& prefix, Import& intp, tuple<string,Thm,CTerm,string> const& obtain, Resolver& infer, bool unprefixed ) {
		auto [org_sym,ex,spec,name] = obtain;
		auto sym = unprefixed || prefix.empty() ? org_sym : prefix+'.'+org_sym;
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
			Thm thm = infer.prove(_thy,stmt,{SIMP});
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
			thy.add_import("_",thy.self(),false);// file root
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
		string name;
		bool unprefixed;
		if( skips("!") ) {// canonical prefix
			prefix = name = get_thm_name();
			unprefixed = false;
		} else {
			prefix = get_thm_name();
			if( skips(":") ) {// explicit prefix
				name = get();
				unprefixed = false;
			} else if( skips("?") ) {// optional prefix
				name = get();
				unprefixed = true;
			} else {// optional canonical prefix
				name = prefix;
				unprefixed = true;
			}
		}
		auto intp = _thy.thy(name,reader());
		auto src = intp.source();
		while( auto const& t = gets_term(1000) ) {
			for(;;) {
				if( auto const& assume = intp.assuming() ) {
					auto infer = _thy.resolver(_out_resolver);
					_auto_discharge(_thy,prefix,intp,*assume,change,infer,unprefixed);
				} else if( auto const& obtain = intp.obtaining() ) {
					auto infer = _thy.resolver(_out_resolver);
					_auto_retain(_thy,prefix,intp,*obtain,infer,unprefixed);
				} else {
					break;
				}
			}
			auto const& fix = intp.fixing();
			if( !fix ) throw Error("\"unexpected instantiation\"")(*t);
			intp.instantiate(_thy.enclose(*t));
		}
		auto path = src.print_name();
		bool success = true;
		if( skips(";") ) {
			if MSG {
				cout << (change ? "importing " : "interpreting ");
				if( !prefix.empty() ) {
					cout << prefix << ": ";
				}
				cout << path << endl;
			}
			_depth++;
			success = _import_loop(prefix,intp,change,unprefixed);
			_depth--;
		} else {
			skip(".");
			for(;;) {
				if( auto const& fix = intp.fixing() ) {
					_auto_instantiate(intp,*fix,change);
				} else if( auto const& assume = intp.assuming() ) {
					auto infer = _thy.resolver(_out_resolver);
					_auto_discharge(_thy,prefix,intp,*assume,change,infer,unprefixed);
				} else if( auto const& obtain = intp.obtaining() ) {
					auto infer = _thy.resolver(_out_resolver);
					_auto_retain(_thy,prefix,intp,*obtain,infer,unprefixed);
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
			if( unprefixed || prefix == "" ) {
				_thy.import_rewrite(src,intp);
				if( !_thy.definer() && src.definer() ) {
					_thy.setup_definer(src.definer()->beta().subst(intp));
				}
			}
			_thy.add_import(prefix,std::move(intp),unprefixed);
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
	bool _import_loop( string const& prefix, Import& intp, bool change, bool unprefixed ) {
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
							auto infer = _thy.resolver(_out_resolver);
							_auto_discharge(org_thy,prefix,intp,*assume,change,infer,unprefixed);
						} else if( auto const& obtain = intp.obtaining() ) {
							auto infer = _thy.resolver(_out_resolver);
							_auto_retain(org_thy,prefix,intp,*obtain,infer,unprefixed);
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
						auto infer = _thy.resolver(_out_resolver);
						_auto_retain(org_thy,prefix,intp,*obtain,infer,unprefixed);
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
							auto infer = _thy.resolver(_out_resolver);
							_auto_discharge(org_thy,prefix,intp,*assume,change,infer,unprefixed);
						}
					} else if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& obtain = intp.obtaining() ) {
						auto infer = _thy.resolver(_out_resolver);
						_auto_retain(org_thy,prefix,intp,*obtain,infer,unprefixed);
					} else {
						break;
					}
				}
			} else if( skips("obtain") ) {
				_obtain(org_thy);
			} else if( skips("define") ) {
				_define(org_thy);
			} else if( skips("retain") ) {
				_retain(prefix,intp,change,org_thy,unprefixed);
			} else if( skips("oops") ) {
				return false;
			} else if( auto ctrl = gets_concluder() ) {
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change);
					} else if( auto const& assume = intp.assuming() ) {
						_auto_discharge(org_thy,prefix,intp,*assume,change,*ctrl,unprefixed);
					} else if( auto const& obtain = intp.obtaining() ) {
						_auto_retain(org_thy,prefix,intp,*obtain,*ctrl,unprefixed);
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
		} catch( Term const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			if MSG cout << _indent();
		}
		_thy = org_thy;
		return true;
	}
	void _retain( string const& prefix, Import& intp, bool change, Thy& org_thy, bool unprefixed ) {
		auto sym = get_sym();// the symbol to be instantiated
		auto term = org_thy.cterm( skips(":=") ? get_term() : sym );
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change);
			} else if( auto const& assume = intp.assuming() ) {
				auto infer = _thy.resolver(_out_resolver);
				_auto_discharge(org_thy,prefix,intp,*assume,change,infer,unprefixed);
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
							print_goals(thesis);
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
				auto infer = _thy.resolver(_out_resolver);
				_auto_retain(org_thy,prefix,intp,*obtain,infer,unprefixed);
			} else {
				throw Error("\"unexpected retain\"")(sym);
			}
		}
	}
	Intro make_rule( Thm const& thm ) {
		if( skips(">") ) {
			auto n = get_int();
			bool all = !skips("=");
			return Intro::imp(thm,n,all);
		}
		if( skips("=") ) {
			return Intro::imp(thm,0,false);
		} else {
			return Intro::rule(thm);
		}
	}
	Opt<Resolver> gets_concluder() {
		if( skips("by") ) {
			auto resolver = _thy.resolver(_out_resolver);
			while( auto thm = gets_thm() ) {
				resolver.inflate(_thy,*thm);
				if( auto cs = gets_claim_status() ) {
					add_claim(_thy,{},cs,*thm);
				} else {
					add_intro(_thy,*thm,true);
				}
			}
			while( skips("#") ) {
				if( skips("weak") ) {
					while( auto thm = gets_thm() ) {
						add_intro(_thy,*thm,false);
					}
				} else if( skips("elim") ) {
					while( auto thm = gets_thm() ) {
						_thy.add_thm(ELIM,*thm,Elim::rule(*thm,0,'?'));
					}
				} else if( int type = skips("simp") ? 1 : skips("fold") ? 2 : skips("cong") ? 3 : 0 ) {
					while( auto const& thm = _gets_thm(_thy) ) {
						auto rule = *thm;
						if( type == 2 ) {
							rule = _thy.dualize(rule,resolver);
						}
						if PRF {
							if( !MSG ) cout << _indent(' ');
							cout << "adding rewrite rule: " << _thy.pretty(rule) << endl;
						}
						resolver.rew->add_rewrite_rule(resolver.rules,rule,type==3);
					}
				} else {
					throw Error("\"unexpected\"")(get());
				}
			}
			skip(".");
			return {resolver};
		} else if( skips(".") ) {
			return {_thy.resolver(_out_resolver)};
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
				auto thy = _thy.thy(name,reader()).source();
				cout << thy << endl;
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
				_out_resolver = gets_int().value_or(5);
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
		auto [name,cs] = _get_name_status();
		auto thm = get_thm();
		add_claim(_thy,name,cs,thm);
		if MSG cout << "note " << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
		if( !name && cs ) {
			while( auto o = gets_thm() ) {
				add_claim(_thy,name,cs,*o);
				if MSG cout << "\t" << *cs << _thy.pretty(*o) << endl;
			}
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
	pair<Opt<string>,Opt<ClaimStatus>> _get_name_status() {
		auto ret = pair<Opt<string>,Opt<ClaimStatus>>();
		ret.first = gets( Tokenizer::Word | Tokenizer::Number );
		ret.second = gets_claim_status();
		if( !ret.second ) {
			skip(":");
		}
		return ret;
	}
	function<ostream&(ostream&)> _print_name_status( Opt<string> name, Opt<ClaimStatus> const& cs ) {
		return [&]( ostream& os )->ostream& {
			if( name ) cout << *name;
			if( cs ) {
				os << *cs;
			} else {
				os << ": ";
			}
			return os;
		};
	}
	Opt<tuple<Opt<string>,Opt<ClaimStatus>,Thm>> _state() {
		auto [name,cs] = _get_name_status();
		if MSG {
			cout << "showing " << _print_name_status(name,cs);
		}
		auto assm_thy = _thy.branch();
		bool needthen = false;
		bool vars = false;
		for(;;) {
			if( skips("for") ) {
				needthen = true;
				vars = true;
				if MSG cout << "for" << flush;
				while( auto const& sym = gets_sym() ) {
					if MSG cout << ' ' << *sym << flush;
					assm_thy.fix(*sym);
				}
			} else if( skips("if") ) {
				needthen = true;
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
							add_claim(assm_thy,{},ClaimStatus::INFLATED,assm_thy.assume(t));
							if( !skips(",") ) break;
							if MSG cout << ", " << flush;
						}
						skip("]");
						if MSG cout << " ] ";
					} else {
						auto [name,cs] = _get_name_status();
						auto t = get_term();
						if MSG cout << _print_name_status(name,cs) << _thy.pretty(t) << ", " << flush;
						auto assm = assm_thy.assume(t);
						add_claim(assm_thy,name,cs,assm);
					}
					if( !skips(",") ) break;
				};
			} else {
				break;
			}
		}
		if( needthen ) {
			skip("then");
			if MSG cout << "then ";
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
				add_claim(_thy,name,cs,thm);
				return {{name,cs,thm}};
			} else {
				if ERR cerr << "failed to prove " << cs << thesis.goal();
				return {};
			}
		}
		skip(".");
		auto thm = assm_thy.prove(goal).intro();
		add_claim(_thy,name,cs,thm);
		return {{name,cs,thm}};
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
	struct Fix : string {};
	struct Assume {
		Opt<string> name;
		Opt<ClaimStatus> cs;
		Opt<Term> assm;
	};
	struct GoalPat {
		Opt<string> name;
		Opt<ClaimStatus> cs;
		vector<Sum<Fix,Assume>> decls;
		Opt<Term> concl;
		bool proof;
	};
	GoalPat _get_subgoal() {
		auto ret = GoalPat();
		for(;;) {
			if( skips("for") ) {
				while( auto o = gets_sym() ) {
					ret.decls.emplace_back(Fix{*o});
				}
			} else if( skips("if") ) {
				do {
					auto name = gets( Tokenizer::Word | Tokenizer::Number );
					auto const& cs = gets_claim_status();
					auto assm = cs ? gets_term() : skips(":") ? Opt<Term>{get_term()} : Opt<Term>();
					ret.decls.emplace_back(Assume{name,cs,assm});
				} while( skips(",") );
			} else {
				break;
			}
		}
		if( skips("then") ) {
			ret.concl = {get_term()};
		}
		ret.proof = skips(".") ? false :
			ret.decls.empty() && !ret.concl ? true : (skip(";"), true);
		return ret;
	}
	/** @return first whether the goal pattern matches, and then the theorem if the proof was not aborted. */
	pair<bool,Opt<Thm>> goal_matches( GoalPat const& pat, CTerm const& goal ) {
		auto loc = _thy.branch();
		auto to_loc = *loc.parent();
		auto loc_goal = goal.subst(to_loc);
		auto css = vector<pair<Opt<string>,Opt<ClaimStatus>>>();
		for( auto const& decl : pat.decls ) {
			if( auto const& var = decl.ref<Fix>() ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) {
					return {false,{}};
				}
				loc_goal = all->inst(loc.fix(*var));
			} else if( auto const& p = decl.ref<Assume>() ) {
				auto const& [name,cs,stmt] = *p;
				if( stmt ) {
					size_t prev = loc.revision();
					auto assm = loc.assume(*stmt);
					while( auto const& v = loc.fixed(prev) ) {
						auto all = loc_goal.cunary(ALL);
						if( !all || !all->bind() ) {
							return {false,{}};
						}
						loc_goal = all->inst(loc.cterm(*v));
						prev++;
					}
					auto imp = loc_goal.cbinary(IMP);
					if( !imp || *stmt != imp->first ) {
						return {false,{}};
					}
					add_claim(loc,name,cs,assm);
					loc_goal = imp->second;
				} else {
					auto imp = loc_goal.cbinary(IMP);
					if( !imp ) {
						return {false,{}};
					}
					auto assm = loc.assume(imp->first);
					add_claim(loc,name,cs,assm);
					loc_goal = imp->second;
				}
				css.emplace_back(name,cs);
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
				cout << "show: ";
				auto csi = css.begin();
				if( auto n = loc.revision() ) {
					for( size_t i = 0; i < n; ) {
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
							cout << "if " << _print_name_status(csi->first,csi->second) << _thy.pretty(*assm);
							for(;;) {
								i++;
								csi++;
								auto const assm = loc.assumed(i);
								if( !assm ) break;
								cout << ", " << _print_name_status(csi->first,csi->second) << _thy.pretty(*assm);
							}
							cout << ' ';
							continue;
						}
						assert(false);
					}
					cout << "then ";
				}
				cout << _thy.pretty(loc_goal) << endl;
			}
			auto thesis = Thesis::claim_exact(loc,loc_goal);
			_depth++;
			if MSG cout << _indent();
			auto thm = _prove(thesis);
			_depth--;
			if( !thm ) return {true,{}};
			Thm ret = thm->intro();
			add_claim(_thy,pat.name,pat.cs,ret);
			return {true,{ret}};
		}
		auto infer = loc.resolver(_out_resolver);
		Thm ret = infer.prove(loc,loc_goal,{SIMP}).intro();
		add_claim(_thy,pat.name,pat.cs,ret);
		return {true,{ret}};
	}
	CTerm _get_assm( Thy const& org_thy ) {
		Ctxt assm_loc = org_thy.Ctxt::fork().ctxt();
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
		return assm_loc.enclose(get_term()).intro();
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
				auto const& [name,cs,thm] = *o;
				cout << "proved " << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
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
				if STA print_goal(thesis,"goal: ");
			} else if( skips("goals") ) {
				skip(".");
				if STA print_goals(thesis);
			} else if( skips("have") ) {
				_state();
				if MSG print_goals(thesis);
			} else if( skips("show") ) {
				if( auto o = _state() ) {
					auto [name,cs,thm] = *o;
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
				bool normalize, wide;
				if( skips("+") ) {
					max = 255; normalize = true; wide = true;
				} else {
					max = 0; normalize = false; wide = true;
				}
				auto rules = set<Intro>();
				while( auto thm = gets_thm() ) {
					rules.emplace(make_rule(*thm));
				}
				min = rules.size();
				if( max == 0 ) max = min;
				bool more = _proof_follows();
				thesis.apply(rules,min,max,normalize,wide);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals(thesis,"applied goals:\n\t");
			} else if( skips("simp") ) {
				auto resolver = _thy.resolver(_out_resolver);
				auto& rew = _thy.rewriter(SIMP);
				while( auto thm = gets_thm() ) {
					rew.add_rewrite_rule(resolver.rules,*thm,false);
				}
				bool more = _proof_follows();
				resolver.rewrites(thesis,{SIMP},1,255,true,{},{});
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, "simplified goals:\n\t" );
			} else if( int mode = skips("unfold") ? 1 : skips("fold") ? 2 : 0 ) {
				auto inf = _thy.resolver(_out_resolver);
				auto ctrl = _get_rewrite( inf, _thy, mode == 2 );
				bool more = _proof_follows();
				inf.rewrites(thesis,{},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos,ctrl.rel);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, mode == 2 ? "folded goals:\n\t" : "unfolded goals:\n\t" );
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
				if MSG print_goals(thesis,"next goals ");
			} else if( auto infer = gets_concluder() ) {
				return infer->discharge_all(thesis);
			} else if( skips("use") ) {
				auto thy2in = _thy.fork();
				auto in = thy2in.ctxt();
				auto tmp = in.fix("#TMP");
				auto facts = vector<Thm>();
				size_t n = 0;
				while( auto const& thm = gets_thm() ) {
					facts.push_back(thm->subst(thy2in));
					n++;
				}
				bool more = _proof_follows();
				auto newgoal = tmp;
				while( n > 0 ) {
					n--;
					newgoal = facts[n] >>= newgoal;
				}
				auto goal = in.assume(newgoal);// φ ⟹ ... ⟹ #TMP
				for( auto const& fact : facts ) {
					goal = goal.impE(fact);
				}// goal = #TMP
				auto rule = Intro::rule(goal.intro());
				thesis.apply(rule);
				if( !more ) return thesis.discharge_all();
				if MSG print_goal( thesis, "used goal: " );
			} else if( skips("oops") ) {
				return {};
			} else if( skips("") ) {
				cerr << location() << ": Unexpected EOF" << endl;
				exit(0);
			} else {
				throw Error("\"unexpected\"")(get());
			}
			if MSG cout << _indent();
		} catch ( Term const& e ) {
			if( _through_error ) throw e;
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if MSG cout << _indent();
		}
	}
	void loop() {
		for(;;) try {
			if( _stats() || _thy_decl() || _shared_decl() ) {
			} else if( skips("set") ) {
				if( int mode = skips("simp") ? 1 : skips("rule") ? 2 : 0 ) {
					auto& rew = _thy.modify_rewriter( mode == 1 ? SIMP : RULIFY );
					bool def = skips("!");
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					Thm trans = get_thm();
					if MSG cout << "registering " << ( mode == 1 ? "simplifier" : "rulifier" ) <<
						":\n\timp: " << _thy.pretty(imp) <<
						"\n\trev: " <<  _thy.pretty(revimp) <<
						"\n\trefl: " << _thy.pretty(refl) <<
						"\n\ttrans: " << _thy.pretty(trans);
					rew.register_refl(refl,def);
					rew.register_imp(imp,true);
					rew.register_imp(revimp,false);
					rew.register_trans(trans);
					if MSG cout << endl;
				} else if( skips("trans") ) {
					if MSG cout << "registering transitivity: ";
					auto& rew = _thy.modify_rewriter(SIMP);
					while( auto const& thm = gets_thm() ) {
						rew.register_trans(*thm);
						if MSG cout << _thy.pretty(*thm);
					}
					if MSG cout << endl;
				} else if( skips("to_true") ) {
					auto thm = get_thm();
					if MSG cout << "registering to_true: " << _thy.pretty(thm) << endl;
					auto& rew = _thy.modify_rewriter(SIMP);
					rew.register_to_true(thm);
				} else if( skips("define") ) {
					Thm const& beta = get_thm();
					if MSG cout << " beta: " << _thy.pretty(beta) << endl;
					_thy.setup_definer(beta);
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
			} else if( skips("syntax") ) {
				auto opener = get();
				if( skips("_") ) {
					if( skips(".") ) {
						skip("_");
						auto closer = get();
						skip(":=");
						auto actual = get_sym();
						_thy.modify_syntax().compr(opener,closer,actual);
						if MSG cout << "comprehension: " << opener << "x. y" << closer << " := " << _thy.pretty(actual) << " (x. y)" << endl;
					} else {
						auto next = get();
						if( skips("_") ) {
							skip(".");
							skip("_");
							if( skips(":=") ) {
								auto actual = get_sym();
								_thy.modify_syntax().binder_mid(opener,next,actual);
								if MSG cout << "binder middle " << opener << " x " << next << " y. z := " << actual << " y (x. z)" << endl;
							} else {
								auto closer = get();
								skip(":=");
								auto actual = get_sym();
								_thy.modify_syntax().bcompr(opener,next,closer,actual);
								if MSG cout << "bounded comprehension: " << opener << "x " << next << "y. z" << closer << " := " << _thy.pretty(actual) << " y (x. z)" << endl;
							}
						} else {
							skip(":=");
							auto actual = get_sym();
							_thy.modify_syntax().singleton_compr(opener,next,actual);
							if MSG cout << "singleton comprehension: " << opener << " x " << next << " := " << _thy.pretty(actual) << " x" << endl;
						}
					}
				} else {
					auto closer = get();
					skip(":=");
					auto actual = get_sym();
					_thy.modify_syntax().empty_compr(opener,closer,actual);
					if MSG cout << "empty comprehension: " << opener << ' ' << closer << " := " << _thy.pretty(actual) << endl;
				}
				skip(".");
			} else if( skips("binder") ) {
				string sym = get();
				int llevel = get_int();
				int rlevel = get_int();
				_make_own_parser();
				_thy.modify_syntax().binder(sym,llevel,rlevel);
				if MSG cout << "new binder: " << sym << endl;
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
					auto [name,cs] = _get_name_status();
					auto assm = _get_assm(_thy);
					Thm thm = name ? _thy.add_assm(*name,assm) : _thy.assume(assm);
					add_claim(_thy,name,cs,thm);
					if CTXT {
						if( !MSG ) cout << _indent(' ');
						cout << "assumed " << _print_name_status(name,cs) << _thy.pretty(assm) << ". " << endl;
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
		} catch ( Term const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			if MSG cout << _indent();
		}
	}
	void _obtain( Thy& org_thy ) {
		auto t = get_term(1000);
		auto sym = t.sym();
		if( !sym ) throw Error("\"expected a symbol\"")(t);
		vector<CTerm> props;
		vector<tuple<Opt<string>,Opt<ClaimStatus>,Thm>> prop_thms;
		Thy thesis_thy = _thy.branch();
		CTerm var = thesis_thy.fix("_thesis");
		Thy goal_thy = thesis_thy.branch();
		goal_thy.fix(*sym);
		auto props_thy = org_thy.branch();
		props_thy.fix(*sym);
		if MSG cout << "obtaining " << *sym;
		if( skips("where") ) {
			if MSG cout << " where" << endl;
			for(;;) {
				auto [name,cs] = _get_name_status();
				auto assm = _get_assm(props_thy);
				Thm thm = props_thy.assume(assm);
				add_claim(props_thy,name,cs,thm);
				prop_thms.emplace_back(name,cs,thm);
				props.push_back(goal_thy.cterm(assm));
				if MSG cout << '\t' << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
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
			auto [sym_term,deriver] = org_thy.obtain(*sym,*thm,make_spec_name(*sym),true);
			// deriver: ∀thesis. (p ⟹ ... ⟹ thesis) ⟹ thesis
			for( auto const& [name,cs,prop_thm] : prop_thms ) {
				auto const& arg = prop_thm.intro();// props... ⟹ prop_i
				Thm prop = deriver << arg;// prop_i
				add_claim(_thy,name,cs,prop);
			}
			if MSG cout << "obtained " << *sym << endl;
		} else {
			if ERR cout << "failed to obtain " << *sym << endl;
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

void run( istream& is, string const& name, bool exit_on_error, char out, string const& cmddir, string const& locdir ) {
	auto root = Thy("Root",cmddir+"/Root");// the empty root theory, linked to the "Root" directory
	auto lex = Lex();
	init_lex(lex);
	init_syntax(root.modify_syntax());
	Thy dir = root.branch("_dir",locdir);
	Thy thy = dir.branch(name,"");
	root.add_import("Root",root.self(),false);// root
	thy.add_import("_",thy.self(),false);// file root
	auto prover = Prover(thy,is,name,lex,exit_on_error,out,FLAG_SYS,0);
	try {
		prover.loop();
	} catch( Term const& e ) {
		exit(-1);
	}
}

int main(int argc, char* argv[]) {
	bool exit_on_error = false;
	auto cmd = filesystem::path(argv[0]);

	auto cmddir = cmd.parent_path();
	if( argc == 1 ) {
		run(cin,"#stdin",false,FLAGS_DEFAULT,cmddir,filesystem::current_path());
	} else {
		auto file = filesystem::path(argv[1]);
		auto fin = fstream(file);
		run(fin,file.stem(),true,FLAGS_DEFAULT,cmddir,file.parent_path());
	}
	cout << "bye!" << endl;
	return 0;
}

