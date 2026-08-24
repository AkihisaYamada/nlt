#include<fstream>
#include<filesystem>
#include<ranges>
#include<sanitizer/lsan_interface.h>
#include"inference.hpp"
#include"parser.hpp"
#include "util.hpp"

#ifdef __SANITIZE_ADDRESS__
#define EXIT(n) do {\
	__lsan_do_leak_check();\
	__lsan_disable();\
	exit(n); } while(0)
#else
#define EXIT exit
#endif
#define FLAG_ERR (1 << 0)
#define FLAG_SYS (1 << 1)
#define FLAG_STA (1 << 2)
#define FLAG_CTXT (1 << 3)
#define FLAG_THY (1 << 4)
#define FLAG_MSG (1 << 5)
#define FLAG_LOG (1 << 6)
#define FLAG_PROMPT (1 << 7)

#define FLAGS_MIN ( FLAG_SYS | FLAG_STA )
#define FLAGS_CTXT ( FLAGS_MIN | FLAG_CTXT )
#define FLAGS_DEFAULT (FLAGS_CTXT | FLAG_THY | FLAG_MSG)

#define ERR ( _out & FLAG_ERR )
#define SYS ( _out & FLAG_SYS )
#define STA ( _out & FLAG_STA )
#define CTXT ( _out & FLAG_CTXT )
#define THY ( _out & FLAG_THY )
#define MSG ( _out & FLAG_MSG )
#define LOG ( _out & FLAG_LOG )
#define PROMPT if( _out & FLAG_PROMPT ) cout << _indent('>')
#define PR_THY if( THY ) cout << _indent(' ')
#define PR_MSG if( MSG ) cout << _indent(' ')

using namespace std;

string const RULIFY = "#rulify";
string const RULIFY_CONG = "#rcong";

struct IntroClaim {
	unsigned char after = 0;
	unsigned char prems = 255;
	bool strip_all = true;
	bool weak = false;
};
bool operator<( IntroClaim const& x, IntroClaim const& y ) {
	return x.after < y.after || x.prems < y.prems || x.strip_all < y.strip_all;
}
ostream& operator<<( ostream& os, IntroClaim const& cs ) {
	os << "#intro";
	char const* post = "";
	char const* pre = "[";
	if( cs.prems != 255 ) {
		os << pre << "prems " << (int)cs.prems;
		post = "]";
		pre = ", ";
	}
	if( cs.after > 0 ) {
		os << pre << "after " << (int)cs.after;
		post = "]";
		pre = ", ";
	}
	return os << post;
}
struct SimpClaim {
	unsigned char after = 0;
	bool dual = false;
};
bool operator<( SimpClaim const& x, SimpClaim const& y ) {
	return x.after < y.after || x.dual < y.dual;
}
ostream& operator<<( ostream& os, SimpClaim const& cs ) {
	os << "#simp";
	if( cs.after > 0 ) os << "[after " << (int)cs.after << ']';
	return os;
}

struct ElimClaim {
	unsigned char guards = 0;
};
bool operator<( ElimClaim const& x, ElimClaim const& y ) {
	return x.guards < y.guards;
}
ostream& operator<<( ostream& os, ElimClaim const& cs ) {
	os << "#elim";
	if( cs.guards > 0 ) os << "[guards " << (int)cs.guards << ']';
	return os;
}

enum class OtherClaim {
	REFL, DUAL, TRANS,
	CONG, CONG_WEAK, REWRITE_IMP, REWRITE_REV,
	RULE, RULE_CONG
};
ostream& operator<<( ostream& os, OtherClaim const& cs ) {
	switch( cs ) {
		case OtherClaim::REFL: return os << "#refl";
		case OtherClaim::TRANS: return os << "#trans";
		case OtherClaim::DUAL: return os << "#dual";
		case OtherClaim::CONG: return os << "#cong";
		case OtherClaim::CONG_WEAK: return os << "#cong?";
		case OtherClaim::REWRITE_IMP: return os << "#rewrite_imp";
		case OtherClaim::REWRITE_REV: return os << "#rewrite_rev";
		case OtherClaim::RULE: return os << "#rule";
		case OtherClaim::RULE_CONG: return os << "#rule_cong";
		default: assert(false);
	}
}

using ClaimStatus = set<Sum<IntroClaim,SimpClaim,ElimClaim,OtherClaim>>;

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	if( cs.empty() ) return os << ':';
	for( auto const& c : cs ) {
		if( auto const& intro = c.ref<IntroClaim>() ) {
			os << *intro;
		} else if( auto const& simp = c.ref<SimpClaim>() ) {
			os << *simp;
		} else if( auto const& elim = c.ref<ElimClaim>() ) {
			os << *elim;
		} else if( auto const& other = c.ref<OtherClaim>() ) {
			os << *other;
		} else {
			assert(false);
		}
	}
	return os;
}

Pair<fstream,string> file_of_thy( string_view const& dir, string_view const& name ) {
	auto path = string(dir);
	path+=name;
	path+=".nl";
	return {fstream(path),std::move(path)};
}

void init_lex( Lex& lex ) {
	lex.register_char('_',Lex::Underscore);
	lex.register_char('\'',Lex::Quote);
	lex.register_char('!',Lex::MultiOp);
	lex.register_range('#','&',Lex::MultiOp);
	lex.register_range('*','+',Lex::MultiOp);
	lex.register_char(',',Lex::LEFTOP);
	lex.register_char('-',Lex::MultiOp);
	lex.register_char('/',Lex::MultiOp);
	lex.register_char(':',Lex::MultiOp);
	lex.register_char(';',Lex::LEFTOP);
	lex.register_range('<','@',Lex::MultiOp);
	lex.register_char('\\',Lex::MultiOp);
	lex.register_char('^',Lex::MultiOp);
	lex.register_char('`',Lex::MultiOp);
	lex.register_char('|',Lex::MultiOp);
	lex.register_char('~',Lex::MultiOp);
}
void init_syntax( Syntax& syntax ) {
	syntax.infix(":",":",30,31,30,{});
	syntax.infix(",",",",-20,-19,-20,{});
	syntax.infix(";",";",-30,-29,-30,{});
	syntax.infix(":=",":=",-1,-1,-2,{});
	syntax.prefix("if","if",-1,-2);
	syntax.infix("then","then",-2,-1,-2,{});
	syntax.infix("else","else",-2,-2,-1,{});
	syntax.prefix("for","for",-1,-1);
	syntax.compr("begin","end","begin",-1);

}

static Error const ProofMismatch = Error("#proof-mismatch");

class Prover : public Parser {
	Thy _thy;
	Lex& lex;
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
	Prover( Thy const& thy, istream& is, std::filesystem::path const& filename, Lex& lex, bool through_error, char out, char out_load, unsigned char depth ) :
		_depth(depth),
		_thy(thy),
		lex(lex),
		Parser(is,(string)filename,lex),
		_through_error(through_error),
		_out(out),
		_out_load(out_load) {
		PROMPT;
	}
	Syntax const& syntax() const {
		return _thy.syntax();
	}
	Thy& thy() & {
		return _thy;
	}
	Opt<Thm> gets_thm() {
		return _gets_thm(_thy,true);
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
	RewriteCtrl _get_rewrite( Resolver& resolver, Thy& loc, bool rev, bool normalize ) {
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
		ret.normalize = rep == 0 && normalize || skips("!");
		while( auto const& arg = _gets_thm(loc,true) ) {
			auto rule = *arg;
			if( rev ) {
				rule = loc.dualize(rule,resolver);
			}
			resolver.rew->add_rewrite_rule(resolver.rules,rule,false);
		}
		if( rep > 0 ) {
			ret.min = ret.max = rep;
		} else if( ret.normalize ) {
			ret.max = 255;
		}
		return ret;
	}
	auto reader() const& {
		return [&]( Thy& thy, istream& fis, std::filesystem::path const& filepath ){
			if SYS {
				cout << _indent(' ') << "loading " << filepath << endl;
			}
			Prover(thy,fis,filepath,lex,true,_out_load,_out_load,_depth+1).loop();
			if ( SYS && _out_load & (FLAG_CTXT|FLAG_THY) ) {
				cout << _indent(' ') << "loaded " << filepath << endl;
			}
		};
	}
	Opt<Thm> _gets_thm( Thy& thy, bool root ) {
		auto const& opt = gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = skips("/") ? [&]{// name is a theory name
			auto loc = thy.thy(*opt,reader()).source();
			auto name = get_thm_name();
			while( skips("/") ) {
				loc = loc.thy(name,reader()).source();
				name = get_thm_name();
			}
			Thm ret = loc.thm(name);
			while( ret.ctxt() != thy ) {
				ret = ret.intro();
			}
			return ret;
		}() : thy.thm(*opt);
		while( skips("[") ) {
			auto loc = thy.branch();
			auto tmp = loc.weaken(ret);
			for(;;) {
				if( skips("for") ) {
					while( auto x = gets(Lexer::WORD) ) {
						loc.fix(*x);
					}
				} else if( skips("of") ) {
					auto sub = loc.fork();
					auto subctxt = sub.ctxt();
					tmp = tmp.subst(sub);
					auto strip_imp = [&]{
						while( auto imp = tmp.cbinary(IMP) ) {
							tmp = tmp.impE(subctxt.assume(imp->first));
						}
					};
					for(;;) {
						if( skips("_") ) {
							strip_imp();
							auto const& all = tmp.cbinder(ALL);
							if( !all ) throw Error("\"no variable for _\"");
							tmp = tmp.allE(subctxt.fix(std::get<0>(*all)));
						} else if( auto t = gets_term(1000) ) {
							strip_imp();
							tmp = tmp.allE(subctxt.cterm(*t));
						} else {
							break;
						}
					}
					tmp = tmp.intro();
				} else if( skips("OF") ) {
					auto var_ctxt = loc.fork().ctxt();
					auto strip_ctxt = var_ctxt.fork().ctxt();
					auto strip_thm = strip_ctxt.weaken(tmp);
					auto reorder_intp = var_ctxt.fork();
					auto reorder_ctxt = reorder_intp.ctxt();
					auto reorder_prems = vector<Sum<Thm,pair<char,size_t>>>();
					auto args = vector<Thm>();
					auto parent_prems = vector<CTerm>();
					auto head_prems = vector<CTerm>();
					auto tail_prems = vector<CTerm>();
					auto auto_prems = vector<CTerm>();// number of heads to be automatically discharged
					for(;;) {
						strip_thm = strip_all(strip_thm,var_ctxt).first;
						char mode;
						if( skips("_") ) {// assume the premise
							mode = 1;
							reorder_prems.emplace_back(pair{mode,head_prems.size()});
						} else if( skips(">") ) {// move the premise to the last
							mode = 2;
							reorder_prems.emplace_back(pair{mode,tail_prems.size()});
						} else if( skips("!") ) {// discharge
							mode = 3;
							reorder_prems.emplace_back(pair{mode,auto_prems.size()});
						} else if( skips("<") ) {// assume in the parent
							mode = 4;
							reorder_prems.emplace_back(pair{mode,parent_prems.size()});
						} else if( auto const& arg = _gets_thm(loc,false) ) {// unify with the argument
							mode = 0;
							args.emplace_back(*arg);
						} else {
							break;
						}
						auto imp = strip_thm.cbinary(IMP);
						if( !imp ) throw Error("\"no premise\"")(strip_thm);
						strip_thm = strip_thm.impE(strip_ctxt.assume(imp->first));
						auto reorder_prem = reorder_ctxt.weaken(imp->first.lift());
						switch( mode ) {
						case 1:
							head_prems.emplace_back(reorder_prem);
							break;
						case 2:
							tail_prems.emplace_back(reorder_prem);
							break;
						case 3:
							auto_prems.emplace_back(reorder_prem);
							break;
						case 4:
							parent_prems.emplace_back(reorder_prem);
							break;
						case 0:
							reorder_prems.emplace_back(reorder_ctxt.assume(reorder_prem));
							break;
						} 
					}
					// forming reordered theorem
					auto auto_assms = vector<Thm>();
					for( auto const& prem : auto_prems ) {
						auto_assms.emplace_back( reorder_ctxt.assume(prem) );
					}
					auto parent_assms = vector<Thm>();
					for( auto const& prem : parent_prems ) {
						parent_assms.emplace_back( reorder_ctxt.assume(prem) );
					}
					auto head_assms = vector<Thm>();
					for( auto const& prem : head_prems ) {
						head_assms.emplace_back( reorder_ctxt.assume(prem) );
					}
					auto tail_assms = vector<Thm>();
					for( auto const& prem : tail_prems ) {
						tail_assms.emplace_back( reorder_ctxt.assume(prem) );
					}
					auto reorder = Intp::make(strip_ctxt,var_ctxt).compose(reorder_intp);
					for( auto const& prem : reorder_prems ) {
						if( auto thm = prem.ref<Thm>() ) {
							reorder.discharge(*thm);
						} else {
							auto [mode,ind] = *prem.ref<1>();
							switch( mode ) {
							case 1: reorder.discharge(head_assms[ind]); break;
							case 2: reorder.discharge(tail_assms[ind]); break;
							case 3: reorder.discharge(auto_assms[ind]); break;
							case 4: reorder.discharge(parent_assms[ind]); break;
							}
						}
					}
					// obtain the theorem with premises reordered, and then variables quantified 
					tmp = strip_thm.subst(reorder).intro().intro();
					// in particular, premises which will be unified come in front
					for( auto const& arg : args ) {
						tmp = tmp << arg;
					}
					if( !parent_prems.empty() || !auto_prems.empty() ) {
						auto sub = loc.branch();
						tmp = strip_all(sub.weaken(tmp),sub).first;
						// move assumptions to parent
						for( size_t i = 0; i < parent_prems.size(); i++ ) {
							Term prem = ASSERTED(tmp.cbinary(IMP))->first;
							if( root ) throw Error("\"Cannot move assumption up\"")(prem);
							tmp = tmp.impE(sub.weaken(loc.assume(prem)));
						}
						// auto discharge
						for( size_t i = 0; i < auto_prems.size(); i++ ) {
							auto prem = ASSERTED(tmp.cbinary(IMP))->first;
							auto resolver = thy.resolver(_out_resolver);
							tmp = tmp.impE(resolver.prove(sub,prem,{SIMP}));
						}
						tmp = tmp.intro();
					}
				} else if( skips("THEN") ) {
					auto sub = loc.branch();
					auto tmp2 = sub.weaken(tmp); // φ ⟹... ψ
					auto thm = _get_thm(sub,root);// ψ ⟹ χ
					auto strip_ctxt = sub.fork().ctxt();
					auto [strip_thm,n] = strip_all(strip_ctxt.weaken(thm),strip_ctxt);
					auto imp = strip_thm.cbinary(IMP);
					if( !imp ) throw Error("\"malformed THEN\"")(strip_thm);
					auto cond = imp->first;
					auto arg = strip_ctxt.weaken(tmp2);
					for(;;){
						arg = strip_all(arg,strip_ctxt).first;
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
					tmp = thm.impE(arg.subst(strip2sub)).intro();
				} else if( int mode = skips("unfold") ? 1 : skips("fold") ? 2 : 0 ) {
					auto resolver = loc.resolver(_out_resolver);
					auto ctrl = _get_rewrite(resolver,loc,mode==2,false);
					tmp = resolver.rewrites(loc,tmp,{},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos);
				} else if( skips("simp") ) {
					auto const& rew = loc.rewriter(SIMP);
					auto resolver = Resolver(rew,_out_resolver);
					auto ctrl = _get_rewrite(resolver,loc,false,true);
					while( auto thm = _gets_thm(loc,true) ) {
						rew.add_rewrite_rule(resolver.rules,*thm,false);
					}
					tmp = resolver.rewrites(loc,tmp,{SIMP},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos);
				} else if( skips("rule") ) {
					auto const& rew = loc.rewriter(RULIFY);
					auto resolver = Resolver(rew,_out_resolver);
					tmp = resolver.rewrites(loc,tmp,{RULIFY},1,255,true,{});
				} else if( skips("dual") ) {
					auto resolver = Resolver({},_out_resolver);
					tmp = loc.dualize(tmp,resolver);
				} else break;
				if( !skips(",") ) break;
			}
			skip("]");
			ret = tmp.intro();
		}
		return ret;
	}
	Thm _get_thm( Thy& loc, bool root ) {
		auto ret = _gets_thm(loc,root);
		if( !ret ) throw Error("\"expected a theorem\"")(get());
		return *ret;
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		while( auto const& name = gets_thm_name() ) {
			skip(":");
			Thm const& thm = get_thm();
			ret.emplace(*name,thm);
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
	function<ostream&(ostream&)> _indent( char c ) const & {
		return [c,this]( ostream& os )->ostream& {
			for( int i = 0; i <= _depth; i++ ) {
				os << c;
			}
			return os << ' ' << flush;
		};
	}
	void _get_intro_mod( IntroClaim& intro ) {
		if( skips("[") ) {
			do {
				if( skips("after") ) {
					intro.after = get_int();
				} else if( skips("prems") ) {
					intro.prems = get_int();
				} else if( skips("no_expand") ) {
					intro.strip_all = false;
				} else break;
			} while( skips(",") );
			skip("]");
		}
	}
	bool gets_claim_status( ClaimStatus& cs ) {
		if( skips("!") ) {
			cs.emplace(IntroClaim());
		} else if( skips("?") ) {
			cs.emplace(IntroClaim{.weak=true});
		} else if( skips("#") ) {
			do {
				if( skips("intro") ) {
					IntroClaim intro;
					_get_intro_mod(intro);
					cs.emplace(intro);
				} else if( skips("weak") ) {
					IntroClaim intro{.weak=true};
					_get_intro_mod(intro);
					cs.emplace(intro);
				} else if( skips("simp") ) {
					unsigned char after = 0;
					if( skips("[") ) {
						if( skips("after") ) {
							after = get_int();
						}
						skip("]");
					}
					cs.emplace( SimpClaim{.after=after} );
				} else if( skips("elim") ) {
					unsigned char guards = 0;
					if( skips("[") ) {
						if( skips("guards") ) {
							guards = get_nat([]( size_t n ){ return n < 128; });
						}
						skip("]");
					}
					cs.emplace( ElimClaim{.guards=guards} );
				} else if( skips("cong") ) {
					cs.emplace( skips("?") ? OtherClaim::CONG_WEAK : OtherClaim::CONG );
				} else if( skips("rule" ) ) {
					cs.emplace( OtherClaim::RULE );
				} else if( skips("rule_cong") ) {
					cs.emplace( OtherClaim::RULE_CONG );
				} else if( skips("refl") ) {
					cs.emplace( OtherClaim::REFL );
				} else if( skips("dual") ) {
					cs.emplace( OtherClaim::DUAL );
				} else if( skips("trans") ) {
					cs.emplace( OtherClaim::TRANS );
				} else if( skips("rewrite_imp") ) {
					cs.emplace( OtherClaim::REWRITE_IMP );
				} else if( skips("rewrite_rev") ) {
					cs.emplace( OtherClaim::REWRITE_REV );
				} else {
					throw Error("\"unknown rule\"")(peek_token());
				}
			} while( skips("#") );
		} else {
			return false;
		}
		return true;
	}
	void add_claim( Thy& loc, Opt<string> const& name, ClaimStatus const& cs, Thm const& thm ) {
		ThmInfo info = {};
		for( auto mode : cs ) {
			if( auto const& intro = mode.ref<IntroClaim>() ) {
				if( intro->after > 0 ) {
					info = {Elim::rule( thm, 0, intro->after-1, intro->weak ? '?' : '!' )};
					loc.add_thm(INFLATOR,thm,info);
				} else {
					info = {Intro::imp(thm,intro->prems,intro->strip_all)};
					Resolver({},_out_resolver).add_intro(loc,*info.ref<Intro>(),!intro->weak);
				}
			} else if( auto const& simp = mode.ref<SimpClaim>() ) {
				Thm thm2 = simp->dual ? [&]{
					auto resolver = Resolver({},_out_resolver);
					return loc.dualize(thm,resolver);
				}() : thm;
				if( simp->after > 0 ) {
					info = {Elim::rule(thm2,0,simp->after-1,'=')};
					loc.add_thm(INFLATOR,thm2,info);
				} else {
					auto [ind,rel,rule] = loc.rewriter(SIMP).make_rule(thm2,false);
					info = {rule};
					loc.add_thm(SIMP+rel,thm2,info);
				}
			} else if( auto const& elim = mode.ref<ElimClaim>() ) {
				info = {Elim::rule(thm,elim->guards,0,'!')};
				loc.add_thm(ELIM,thm,info);
			} else if( auto const& other = mode.ref<OtherClaim>() ) {
				switch( *other ) {
				case OtherClaim::DUAL:
					loc.register_dual(thm);
					break;
				case OtherClaim::TRANS:
					loc.register_trans(thm);
					break;
				case OtherClaim::REFL:
					loc.register_refl(thm);
					break;
				case OtherClaim::CONG:
					loc.modify_rewriter(SIMP).register_cong(thm);
					break;
				case OtherClaim::CONG_WEAK:
					loc.modify_rewriter(SIMP).register_fallback(thm);
					break;
				case OtherClaim::REWRITE_IMP:
					loc.register_imp(thm,true);
					break;
				case OtherClaim::REWRITE_REV:
					loc.register_imp(thm,false);
					break;
				case OtherClaim::RULE: {
					auto [ind,rel,rule] = loc.rewriter(RULIFY).make_rule(thm,false);
					info = {rule};
					loc.add_thm(RULIFY+rel,thm,info);
				} break;
				case OtherClaim::RULE_CONG:
					loc.modify_rewriter(RULIFY).register_cong(thm);
					break;
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
		cout << _indent(' ');
		while( i < thesis.goal_count() ) {
			auto const& imp = acc.binary(IMP);
			i++;
			cout << pre << i << ". " << _thy.pretty(imp->first) << endl;
			acc = imp->second;
			pre = "\t";
		}
		if( i == 0 ) {
			cout << "QED" << endl;
		}
	}
	void print_goal( Thesis const& thesis, string_view const& pre ) {
		if( auto goal = thesis.has_goal() ) {
			cout << pre << _thy.pretty(*goal) << endl;
		} else {
			cout << "QED" << endl;
		}
	}
	void _auto_instantiate(
		Import& intp, string const& sym, bool change,
		vector<CTerm>::const_iterator& inst_it, vector<CTerm>::const_iterator inst_end
	) {
		if( inst_it != inst_end ) {
			intp.instantiate(*inst_it);
			inst_it++;
		} else {
			if( auto const& c = _thy.constant(sym) ) {
				intp.instantiate(*c);
			} else if( change ) {
				auto const& c = _thy.fix(sym);
				intp.instantiate(c);
				if CTXT cout << _indent(' ') << "fixed " << _thy.pretty_sym(sym) << endl;
			} else throw Error("\"auto instantiate failed\"")(sym);
		}
	}
	Thy::ThmTest exact( Term const& assm ) {
		return [assm,this]( Import const& import, string_view const& name, Thm const& thm, ThmInfo const& info )->Opt<Thm>{
			auto thm2 = thm.subst(import);
			if( thm2 == assm ) {
				return {thm2};
			}
			return {};
		};
	}
	void _auto_discharge( Thy& org_thy, Opt<string const&> prefix, Import& intp, Pair<CTerm,string> const& assume, bool change, Resolver& infer ) {
		auto const& assm = assume.first;
		auto assm_name = assume.second;
		auto disp = [&]( ostream& os )->ostream& {
			return os << assm_name << ": " << _thy.pretty(assm) << endl;
		};
		if( auto const& o = _thy.find_thm(assm_name,exact(assm)) ) {
			intp.discharge(*o);
			PR_MSG << "transferred " << disp;
			return;
		}
		if( prefix ) {
			assm_name = *prefix + '.' + assm_name;
			if( auto const& o = _thy.find_thm(assm_name,exact(assm)) ) {
				intp.discharge(*o);
				PR_MSG << "transferred " << disp;
				return;
			}
		}
		if( change ) {
			Thm ret = org_thy.add_assm(assm_name,assm);
			intp.discharge(ret);
			if CTXT cout << _indent(' ') << "admitted " << disp;
			return;
		}
		PR_MSG << "blasting " << disp;
		Thm ret = infer.prove(_thy,assm,{SIMP});
		intp.discharge(ret);
	}
	void _auto_retain( Thy& org_thy, Opt<string const&> thm_prefix, Opt<string const&> sym_prefix, Import& intp, tuple<string,Thm,CTerm,string> const& obtain, Resolver& infer ) {
		auto [org_sym,ex,spec,org_name] = obtain;
		auto sym = sym_prefix ? *sym_prefix + '.' + org_sym : org_sym;
		auto name = thm_prefix ? *thm_prefix + '.' + org_name : org_name;
		if( auto csym = _thy.constant(sym) ) {
			CTerm const& stmt = spec.inst(*csym);
			if( auto const& o = _thy.find_thm(name,exact(stmt)) ) {
				intp.retain(*csym,*o);
			} else {
				PR_MSG << "blasting " << name << ": " << _thy.pretty(stmt) << endl;
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
		auto resolver = Resolver();
		while( auto obtain = p->obtaining() ) {
			auto const& [sym,ex,spec,name] = *obtain;
			auto [sym_term,thm] = child.obtain(sym,ex,name,false);
			p->retain(sym_term,thm);
		}
	}
	static auto _mkpath( Opt<string const&> prefix ) {
		return prefix ?
			(function<string(string const&)>)[&]( string const& name ){ return *prefix + '.' + name; } :
			[&]( string const& name )->string{ return name; };
	}
	void _auto_import(
		Opt<string const&> thm_prefix, Opt<string const&> sym_prefix, Import& intp, bool change,
		vector<CTerm>const& insts
	){
		auto inst_it = insts.begin();
		auto inst_end = insts.end();
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change,inst_it,inst_end);
			} else if( auto const& assume = intp.assuming() ) {
				auto infer = _thy.resolver(_out_resolver);
				_auto_discharge(_thy,thm_prefix,intp,*assume,change,infer);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto infer = _thy.resolver(_out_resolver);
				_auto_retain(_thy,thm_prefix,sym_prefix,intp,*obtain,infer);
			} else {
				break;
			}
		}
		if( inst_it != inst_end ) {
			throw Error("\"unexpected instantiate\"")(*inst_it);
		}
	}
/*
	void _emulate_import( Opt<string const&> thm_prefix, Import& intp, Subst const& org ){
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				auto const& ot = org.get(*fix);
				auto const& t = ot ? (Term)*ot : *fix;
				auto ct = _thy.closed(t);// TODO: in case of o, should be known to be closed
				if( !ct ) throw Error("failed to update fix")(*fix);
				intp.instantiate(*ct);
			} else if( auto const& assume = intp.assuming() ) {
				auto const& [assm,name] = *assume;
				auto path = _mkpath(thm_prefix)(name);
				auto o = _thy.find_thm(path,exact(assm));
				if( !o ) throw Error("\"failed to update import assumption\"")(path)(assm);
				intp.discharge(*o);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto [src_sym,ex,spec,src_name] = *obtain;
				auto path = _mkpath(thm_prefix)(src_name);
				auto const& ot = org.get(src_sym);
				auto const& t = ot ? (Term)*ot : src_sym;
				auto ct = _thy.closed(t);// TODO: in case of o, should be known to be closed
				if( !ct ) throw Error("\"failed to know replacement\"")(src_sym)(spec);
				auto assm = spec.Term::inst(*ct);
				auto o = _thy.find_thm(path,exact(assm));
				if( !o ) throw Error("\"failed to transfer specification\"")(Term(":=")(src_sym)(t))(assm);
				intp.retain(*ct,*o);
			} else {
				break;
			}
		}
	}
*/
	struct ImportPrefix {
		Opt<string> default_prefix = {};
		Opt<string> optional_prefix = {};
		Opt<string> forced_prefix = {};
		bool canonical_prefix = false;
		bool override = true;
		bool rec = false;
		bool rewrite = true;
	};
	friend ostream& operator<<( ostream& os, ImportPrefix const& pref ) {
		if( pref.forced_prefix ) {
			os << *pref.forced_prefix << ( pref.rec ? "! " : ": " );
		} else if( pref.default_prefix ) {
			os << *pref.default_prefix << "? ";
		} else if( pref.rec ) {
			os << "? ";
		}
		return os;
	}
	Pair<ImportPrefix,string> get_import_prefix() {
		Pair<ImportPrefix,string> ret;
		auto& [pref,name] = ret;
		if( skips("[") ) {
			if( skips("no_rewrite") ) {
				pref.rewrite = false;
			}
			skip("]");
		}
		if( skips("?") ) {// weak unnamed import
			pref.default_prefix = {NONREC_IMPORT};
			pref.canonical_prefix = true;
			pref.override = false;
		} else if( skips("!") ) {// expansive unnamed import
			pref.default_prefix = {""};
			pref.canonical_prefix = true;
			pref.rec = true;
		} else if( skips(":") ) {// canonically qualified import
			pref.canonical_prefix = true;
		} else {
			string str1 = get_thy_name();
			if( skips(":") ) {// qualified import
				pref.forced_prefix = {str1};
			} else if( skips("!") ) {// qualified recursive
				pref.forced_prefix = {str1};
				pref.rec = true;
			} else if( skips("?") ) {// optionally qualified
				pref.default_prefix = {""};
				pref.optional_prefix = {str1};
				pref.override = false;
			} else {// no prefix
				pref.default_prefix = {""};
				pref.canonical_prefix = true;
				name = str1;
				return ret;// unqualified
			}
		}
		name = get_thy_name();
		return ret;
	};
	void add_import( ImportPrefix const& pref, Import const& import ) {
		auto src = import.source();
		_update_parent(src);// in case of interpreting a child.
		if( pref.forced_prefix ) {
			_thy.add_import(*pref.forced_prefix,import,pref.rec,pref.override,pref.rewrite);
		}
		if( pref.default_prefix ) {
			_thy.add_import(*pref.default_prefix,import,pref.rec,pref.override,pref.rewrite);
			if( *pref.default_prefix == "" && _no_syntax ) {// TODO: make elegant
				_no_syntax = false;
				_thy.modify_syntax() = import.source().syntax();
			}
		}
		if( pref.optional_prefix ) {
			_thy.add_import(*pref.optional_prefix,import,pref.rec,pref.override,pref.rewrite);
		}
		if( pref.canonical_prefix ) {
			_thy.add_import(import.source().name(),import,pref.rec,pref.override,pref.rewrite);
		}
	};
	void import( bool change ) {
		auto [pref,name] = get_import_prefix();
		for(;;) {
			auto intp = _thy.thy(name,reader());
			if( intp.source() == _thy ) throw Error("\"self import\"");
			vector<CTerm> insts;
			if( change ) {
				while( auto const& t = gets_term(1000) ) {
					insts.emplace_back(_thy.enclose(*t));
				}
			} else {
				while( auto const& t = gets_term(1000) ) {
					insts.emplace_back(_thy.cterm(*t));
				}
			}
			bool success = true;
			if( skips(";") ) {
				auto const& path = intp.source().print_path();
				PR_MSG << (change ? "importing " : "interpreting ") << pref << path << endl;
				_depth++;
				success = _import_loop(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
				_depth--;
				if( success ) {
					add_import(pref,intp);
					PR_THY << ( change ? "imported " : "interpreted " ) << pref << path << endl;
				}
				return;
			}
			if( skips(",") ) {
				_auto_import(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
				add_import(pref,intp);
				PR_THY << ( change ? "imported " : "interpreted " ) << pref << intp.source().print_path() << endl;
				name = get_thy_name();
				continue;
			} 
			skip(".");
			_auto_import(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
			PR_THY << ( change ? "imported " : "interpreted " ) << pref << intp.source().print_path() << endl;
			add_import(pref,intp);
			return;
		}
	}
	size_t _print_import_goal( Import const& intp, size_t i, string const& pre ) {
		if( auto const& fin = intp.source().finalized() ) {
			if( *fin <= intp.revision() + i ) return 0;
		}
		auto mod = intp.modification(i);
		if( auto const& fix = mod.ref<Import::Fix>() ) {
			cout << _indent(' ') << pre << i+1 << ". instantiate " << _thy.pretty_sym(*fix);
			size_t n = 1;
			while( auto const& fix = intp.modification(i+n).ref<Import::Fix>() ) {
				cout << ", " << _thy.pretty_sym(*fix);
				n++;
			}
			cout << endl;
			return n;
		} else if( auto const& assume = mod.ref<Import::Assume>() ) {
			cout << _indent(' ') << pre << i+1 << ". show " << assume->name << ": " << _thy.pretty(assume->assm) << endl;
			return 1;
		} else if( auto const& obtain = mod.ref<Import::Obtain>() ) {
			cout << _indent(' ') << pre << i+1 << ". retain ";
			if( auto const& o = obtain->spec_name ) {
				cout << _thy.pretty_sym(*o) << ": ";
			}
			cout << _thy.pretty(obtain->spec) << endl;
			return 1;
		} else {
			return 0;
		}
	}
	void _print_import_goals( Import const& intp ) {
		size_t i = 0;
		size_t n = _print_import_goal(intp,i,"  ");
		if( n == 0 ) {
			cout << "no interpretation goals" << endl;
			return;
		}
		for(;;) {
			i += n;
			n = _print_import_goal(intp,i,"  ");
			if( n == 0 ) return;
		}
	}
	struct Fix : string {};
	struct Assume {
		Opt<string> name;
		ClaimStatus cs;
		Opt<Term> assm;
	};
	struct Omit {};
	struct GoalPat {
		Opt<string> name;
		ClaimStatus cs;
		vector<Sum<Fix,Assume,Omit>> decls;
		Opt<Term> concl;
		bool proof;
	};
	GoalPat _get_subgoal( bool show ) {
		auto ret = GoalPat();
		if( show ) {
			ret.name = gets( Tokenizer::WORD | Tokenizer::NUMBER );
			if( !gets_claim_status(ret.cs) ) skip(":");
		}
		bool modified = false;
		for(;;) {
			if( skips("for") ) {
				while( auto o = gets_sym() ) {
					ret.decls.emplace_back(Fix{*o});
				}
				modified = true;
			} else if( skips("if") ) {
				do {
					if( skips("[") ) {
						do {
							ret.decls.emplace_back(Assume{{},{IntroClaim{}},{get_term()}});
						} while( skips(",") );
						skip("]");
						continue;
					}
					if( skips("...") ) {
						ret.decls.emplace_back(Omit{});
						break;
					}
					auto name = gets( Tokenizer::WORD | Tokenizer::NUMBER );
					ClaimStatus cs;
					auto assm = gets_claim_status(cs) ? gets_term() : skips(":") ? Opt<Term>{get_term()} : Opt<Term>();
					ret.decls.emplace_back(Assume{name,cs,assm});
				} while( skips(",") );
				modified = true;
			} else {
				break;
			}
		}
		if( modified ) {
			if( skips("then") ) {
				ret.concl = {get_term()};
			}
		} else if( show ) {
			ret.concl = gets_term();
		} else {
			ret.proof = !skips(".");
			return ret;
		}
		if( ret.proof = skips(";") ) {
		} else {
			skip(".");
		}
		return ret;
	}
	/** @return first whether the goal pattern matches, and then the theorem if the proof was not aborted. */
	Opt<Opt<Thm>> goal_matches( GoalPat const& pat, CTerm const& goal ) {
		auto loc = _thy.branch();
		auto to_loc = *loc.parent();
		auto loc_goal = goal.subst(to_loc);
		auto css = vector<Pair<Opt<string>,ClaimStatus>>();
		for( auto const& decl : pat.decls ) {
			if( auto const& var = decl.ref<Fix>() ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) {
					return {};
				}
				loc_goal = all->inst(loc.fix(*var));
			} else if( auto const& p = decl.ref<Assume>() ) {
				auto const& [name,cs,stmt] = *p;
				if( stmt ) {
					size_t prev = loc.revision();
					auto assm = loc.assume(*stmt);
					while( auto const& v = loc.fixed_at(prev) ) {
						auto all = loc_goal.cunary(ALL);
						if( !all || !all->bind() ) {
							return {};
						}
						loc_goal = all->inst(loc.cterm(*v));
						prev++;
					}
					auto imp = loc_goal.cbinary(IMP);
					if( !imp || *stmt != imp->first ) {
						return {};
					}
					add_claim(loc,name,cs,assm);
					loc_goal = imp->second;
				} else {
					auto imp = loc_goal.cbinary(IMP);
					if( !imp ) {
						return {};
					}
					auto assm = loc.assume(imp->first);
					add_claim(loc,name,cs,assm);
					loc_goal = imp->second;
				}
				css.emplace_back(name,cs);
			} else if( decl.ref<Omit>() ) {
				while( auto const& imp = loc_goal.cbinary(IMP) ) {
					Resolver({},_out_resolver).add_intro(loc,loc.assume(imp->first),true);
					css.emplace_back("!",ClaimStatus{});
					loc_goal = imp->second;
				}
			} else {
				assert(false);
			}
		}
		if( pat.concl ) {
			size_t prev = loc.revision();
			auto concl = loc.enclose(*pat.concl);
			while( auto const& v = loc.fixed_at(prev) ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) return {};
				loc_goal = all->inst(loc.cterm(*v));
				prev++;
			}
			if( loc_goal != concl ) return {};
		}
		if( pat.proof ) {
			if MSG {
				cout << _indent(' ') << "showing";
				auto csi = css.begin();
				if( auto n = loc.revision() ) {
					for( size_t i = 0; i < n; ) {
						if( auto const& v = loc.fixed_at(i) ) {
							cout << " for " << _thy.pretty(*v);
							for(;;) {
								i++;
								auto const& v = loc.fixed_at(i);
								if(!v) break;
								cout << ' ' << _thy.pretty(*v);
							}
							continue;
						}
						if( auto const& assm = loc.assumed_at(i) ) {
							cout << " if" << endl << _indent(' ') << " " << _print_name_status(csi->first,csi->second) << _thy.pretty(*assm);
							for(;;) {
								i++;
								csi++;
								auto const assm = loc.assumed_at(i);
								if( !assm ) break;
								cout << ',' << endl << _indent(' ') << ' ' << _print_name_status(csi->first,csi->second) << _thy.pretty(*assm);
							}
							continue;
						}
						assert(false);
					}
					cout << endl << _indent(' ') << "then";
				}
				cout << ' ' << _thy.pretty(loc_goal) << endl;
			}
			auto thesis = Thesis::claim_exact(loc,loc_goal);
			_depth++;
			PROMPT;
			auto thm = _prove(thesis);
			_depth--;
			if( !thm ) return {{}};
			Thm ret = thm->intro();
			add_claim(_thy,pat.name,pat.cs,ret);
			return {{ret}};
		}
		auto infer = loc.resolver(_out_resolver);
		Thm ret = infer.prove(loc,loc_goal,{SIMP}).intro();
		add_claim(_thy,pat.name,pat.cs,ret);
		return {{ret}};
	}
	Opt<Opt<Thm>> rulify_goal_matches( GoalPat const& pat,CTerm const& assm ) {
		auto thesis = Thesis::claim_exact(_thy,assm); 
		auto rulify = Resolver({_thy.rewriter(RULIFY)}, _out_resolver);
		if( rulify.rewrites(thesis,{RULIFY},0,255,true,false,{},{}) )
		if( auto opt = goal_matches(pat,thesis.goal()) ) {
			if( *opt ) {
				thesis.discharge(**opt);
				return { thesis.concluding() };
			}
			return {{}};
		}
		return {};
	};
	Opt<Thm> _discharge(
		function<Opt<Opt<Thm>>(CTerm const&)> f,
		Import& intp,
		Thy& org_thy,
		Opt<string const&> thm_prefix,
		Opt<string const&> sym_prefix,
		bool change,
		vector<CTerm>::const_iterator& inst_it,
		vector<CTerm>::const_iterator inst_end
	) {
		for(;;) {
			if( auto const& assume = intp.assuming() ) {
				if( auto const& opt = f(assume->first) ) {
					if( *opt ) {
						intp.discharge(**opt);
						if MSG {
							if( _print_import_goal(intp,0,"  ") == 0 ) {
								cout << _indent(' ') << "QED" << endl;
							}
						}
					} else {
						PR_MSG << "aborted " << assume->second << ": " << _thy.pretty(assume->first) << endl;
					}
					return *opt;
				} else {
					auto infer = _thy.resolver(_out_resolver);
					_auto_discharge(org_thy,thm_prefix,intp,*assume,change,infer);
				}
			} else if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change,inst_it,inst_end);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto infer = _thy.resolver(_out_resolver);
				_auto_retain(org_thy,thm_prefix,sym_prefix,intp,*obtain,infer);
			} else {
				throw Error("\"unexpected discharge\"");
			}
		}
	}
	bool _import_loop(
		Opt<string const&> thm_prefix,
		Opt<string const&> sym_prefix,
		Import& intp,
		bool change,
		vector<CTerm> const& insts
	) {
		auto org_thy = _thy;
		_thy = org_thy.scope_temp("#import");// namespace
		auto inst_it = insts.begin();
		auto inst_end = insts.end();
		while( inst_it != inst_end ) {
			auto fix = intp.fixing();
			if( !fix ) break;
			intp.instantiate(*inst_it);
			inst_it++;
		}
		if MSG _print_import_goals(intp);
		for(;;) try {
			PROMPT;
			if( _stats() ) {
			} else if( skips("note") ) {
				_note();
			} else if( skips("goal") ) {
				skip(".");
				_print_import_goal(intp,0,"  ");
			} else if( skips("goals") ) {
				skip(".");
				_print_import_goals(intp);
			} else if( skips("have") ) {
				_state();
			} else if( skips("interpret") ) {
				import(false);
			} else if( skips("instantiate") ) {
				vector<Pair<string,Term>> map;
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
							_auto_discharge(org_thy,thm_prefix,intp,*assume,change,infer);
						} else if( auto const& obtain = intp.obtaining() ) {
							auto infer = _thy.resolver(_out_resolver);
							_auto_retain(org_thy,thm_prefix,sym_prefix,intp,*obtain,infer);
						} else if( auto const& fix = intp.fixing() ) {
							if( *fix == x ) break;
							_auto_instantiate(intp,*fix,change,inst_it,inst_end);
						} else {
							throw Error("\"unexpected instantiate\"")(x);
						}
					}
					intp.instantiate( change ? org_thy.cterm(t) : org_thy.enclose(t) );
					PR_MSG << "instantiated " << x << " := " << _thy.pretty(t) << endl;
				}
			} else if( int mode = skips("-") ? 1 : skips("show") ? 2 : 0 ) {
				auto pat = _get_subgoal( mode == 2 );
				_discharge( [&]( CTerm const& assm ){ return goal_matches(pat,assm); }, intp, org_thy, thm_prefix, sym_prefix, change, inst_it, inst_end );
			} else if( skips("->") ) {
				auto pat = _get_subgoal(false);
				_discharge( [&]( CTerm const& assm ){ return rulify_goal_matches(pat,assm); }, intp, org_thy, thm_prefix, sym_prefix, change, inst_it, inst_end );
			} else if( skips("obtain") ) {
				_obtain(org_thy);
			} else if( skips("define") ) {
				_define(org_thy);
			} else if( skips("retain") ) {
				_retain(thm_prefix,sym_prefix,intp,change,org_thy,inst_it,inst_end);
			} else if( skips("oops") ) {
				return false;
			} else if( auto ctrl = gets_concluder() ) {
				for(;;) {
					if( auto const& fix = intp.fixing() ) {
						_auto_instantiate(intp,*fix,change,inst_it,inst_end);
					} else if( auto const& assume = intp.assuming() ) {
						_auto_discharge(org_thy,thm_prefix,intp,*assume,change,*ctrl);
					} else if( auto const& obtain = intp.obtaining() ) {
						_auto_retain(org_thy,thm_prefix,sym_prefix,intp,*obtain,*ctrl);
					} else {
						break;
					}
				}
				break;
			} else if( skips("") ) {
				cerr << location() << ": Unexpected EOF" << endl;
				EXIT(0);
			} else {
				throw Error("\"Unexpected\"")(get());
			}
		} catch( Term const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			PROMPT;
		}
		if( inst_it != inst_end ) throw Error("\"unexpected instantiate\"")(*inst_it);
		_thy = org_thy;
		return true;
	}
	void _retain(
		Opt<string const&> thm_prefix, Opt<string const&> sym_prefix, Import& intp, bool change, Thy& org_thy,
		vector<CTerm>::const_iterator& inst_it, vector<CTerm>::const_iterator inst_end
	) {
		auto sym = get_sym();// the symbol to be instantiated
		for(;;) {
			if( auto const& fix = intp.fixing() ) {
				_auto_instantiate(intp,*fix,change,inst_it,inst_end);
			} else if( auto const& assume = intp.assuming() ) {
				auto infer = _thy.resolver(_out_resolver);
				_auto_discharge(org_thy,thm_prefix,intp,*assume,change,infer);
			} else if( auto const& obtain = intp.obtaining() ) {
				auto const& [osym,ex,spec,spec_name] = *obtain;
				if( osym == sym ) {
					Thy thesis_loc = _thy.branch();
					auto term = org_thy.cterm( skips(":=") ? get_term() : sym );
					CTerm var = thesis_loc.fix(avoid("thesis",[&](auto x){
						return (bool)_thy.constant(x);
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
					thesis.apply(rule,false);// prop[sym:=term]... ⟹ var
					if( skips(";") ) {
						_depth++;
						if MSG {
							print_goals(thesis);
						}
						PROMPT;
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
					PR_MSG << "retained " << _thy.pretty_sym(sym) << " := " << _thy.pretty(term) << endl;
					break;
				}
				auto infer = _thy.resolver(_out_resolver);
				_auto_retain(org_thy,thm_prefix,sym_prefix,intp,*obtain,infer);
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
				resolver.add_intro(_thy,*thm,true);
			}
			for(;;) {
				ClaimStatus cs;
				if( !gets_claim_status(cs) ) break;
				while( auto thm = gets_thm() ) {
					add_claim(_thy,{},cs,*thm);
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
	unsigned char get_print_level() {
		if( skips("none") ) return 0;
		if( skips("stat") ) return FLAG_STA;
		if( skips("system") ) return FLAG_STA | FLAG_SYS;
		if( skips("ctxt") ) return FLAG_STA | FLAG_SYS | FLAG_CTXT;
		if( skips("thy") ) return FLAG_STA | FLAG_SYS | FLAG_CTXT | FLAG_THY;
		if( skips("log") ) return FLAGS_DEFAULT | FLAG_LOG;
		skips("default");
		return FLAGS_DEFAULT;
	}
	bool _stats() {
		if( int mode = skips("thy") ? 1 : skips("ctxt") ? 2 : 0 ) {
			auto const indent_endl = [this]( ostream& os )->ostream&{ return os << endl << _indent(' '); };
			auto thy = _thy;
			if( !skips(".") ) {
				string name = get();
				thy = thy.thy(name,reader()).source();
				skip(".");
			}
			cout << _indent(' ') << thy.pretty(indent_endl,mode==1) << endl;
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
			string name = gets_thm_name().value_or("");
			string ref = shp ? "#"+name : name;
			cout << "thms " << ref << ":\n" << _thy.print_thms(ref);
			skip(".");
			return true;
		} else if( skips("term") ) {
			int mode = 0;
			if( skips("[") ) {
				if( skips("raw") ) {
					mode = 1;
				} else if( skips("close") ) {
					mode = 2;
				}
				skip("]");
			}
			Term term = get_term();
			skip(".");
			switch( mode ) {
			case 1:
				cout << "term[raw] " << term << endl;
				break;
			case 2: {
				auto cterm = _thy.fork().ctxt().enclose(term).lift();
				cout << "term[close] " << _thy.pretty(cterm) << endl;
			} break;
			default:
				cout << "term " << _thy.pretty(term) << endl;
				break;
			}
			return true;
		} else if( skips("print") ) {
			if( skips("ctxt_id") ) {
				auto b = gets_bool().value_or(true);
				_thy.modify_syntax().print_ctxt(b);
				PR_MSG << "set print ctxt_id" << endl;
			} else if( skips("load") ) {
				_out_load = get_print_level();
				PR_MSG << "set print load level " << _out_load << endl;
			} else if( skips("prover") ) {
				_out_resolver = gets_int().value_or(5);
				PR_MSG << "set print prover level " << endl;
			} else {
				_out = get_print_level();
				PR_MSG << "set print level " << endl;
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
		PR_MSG << "note " << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
		if( !name && !cs.empty() ) {
			while( auto o = gets_thm() ) {
				add_claim(_thy,name,cs,*o);
				PR_MSG << "     " << cs << _thy.pretty(*o) << endl;
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
	Pair<Opt<string>,ClaimStatus> _get_name_status() {
		Pair<Opt<string>,ClaimStatus> ret;
		ret.first = gets( Tokenizer::WORD | Tokenizer::NUMBER );
		if( !gets_claim_status(ret.second) ) {
			skip(":");
		}
		return ret;
	}
	function<ostream&(ostream&)> _print_name_status( Opt<string> name, Opt<ClaimStatus> const& cs ) {
		return [&]( ostream& os )->ostream& {
			if( name ) cout << *name;
			if( cs ) {
				os << *cs << ' ';
			} else {
				os << ": ";
			}
			return os;
		};
	}
	Opt<tuple<Opt<string>,Opt<ClaimStatus>,Thm>> _state() {
		auto [name,cs] = _get_name_status();
		PR_MSG << "showing " << _print_name_status(name,cs);
		auto assm_thy = _thy.branch();
		bool needthen = false;
		bool vars = false;
		for(;;) {
			if( skips("for") ) {
				needthen = true;
				vars = true;
				if MSG cout << "for " << flush;
				while( auto const& sym = gets_sym() ) {
					if MSG cout << *sym << ' ' << flush;
					assm_thy.fix(*sym);
				}
			} else if( skips("if") ) {
				needthen = true;
				if MSG cout << "if" << endl;
				for(;;) {
					if( skips("[") ) {
						PR_MSG << " [ ";
						for(;;) {
							auto t = get_term();
							if MSG cout << _thy.pretty(t);
							add_claim(assm_thy,{},{IntroClaim()},assm_thy.assume(t));
							if( !skips(",") ) break;
							if MSG cout << ", " << flush;
						}
						skip("]");
						if MSG cout << " ] ";
					} else {
						auto [name,cs] = _get_name_status();
						auto t = get_term();
						PR_MSG << ' ' << _print_name_status(name,cs) << _thy.pretty(t);
						auto assm = assm_thy.assume(t);
						add_claim(assm_thy,name,cs,assm);
					}
					if( !skips(",") ) break;
					if MSG cout << ',' << endl;
				};
			} else {
				break;
			}
		}
		if( needthen ) {
			skip("then");
			if MSG cout << endl << _indent(' ') << "then ";
		}
		Term t = get_term(0);
		CTerm goal = assm_thy.enclose(t);
		if MSG cout << _thy.pretty(goal) << endl;
		if( skips(";") ) {
			auto thesis = Thesis::claim_exact(assm_thy,goal);
			_depth++;
			PROMPT;
			auto o = _prove(thesis);
			_depth--;
			if( o ) {
				auto thm = o->intro();
				add_claim(_thy,name,cs,thm);
				return {{name,cs,thm}};
			} else {
				if ERR cerr << "failed to prove " << _print_name_status(name,cs) << thesis.goal();
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
			for(;;) {
				if( skips("as") ) {
					if( name_op ) throw Error("#define")("\"duplicate as\"");
					name_op = get();
				} else {
					break;
				}
			}
			skip("]");
		}
		auto l = get_sym();
		auto name = name_op.value_or(l);
		if( skips(":=") ) {
			Term r = get_term();
			CTerm r_cterm = org_thy.cterm(r);
			skip(".");
			// goal: ∀thesis. (∀l. (∀P. P.[r] ⟹ P.[l]) ⟹ thesis) ⟹ thesis
			auto thesis_ctxt = org_thy.fork().ctxt();
			auto thesis_sym = *avoider(org_thy)("?thesis");
			auto thesis_term = thesis_ctxt.fix(thesis_sym);
			auto l_ctxt = thesis_ctxt.fork().ctxt();
			auto l_cterm = l_ctxt.fix(l);
			auto P = *avoider(org_thy)("P");
			auto lP_ctxt = l_ctxt.fork().ctxt();
			auto P_lP = lP_ctxt.fix(P);
			// fix thesis l P ⊢ P.[r]
			auto Pr = P %= lP_ctxt.weaken(r_cterm);
			// fix thesis l ⊢ ∀P. P.[r] ⟹ P.[l]
			auto spec = (Pr >>= (P %= lP_ctxt.weaken(l_cterm))).lift();
			// fix thesis ⊢ ∀l. (∀P. P.[r] ⟹ P.[l]) ⟹ thesis
			Thm assm = thesis_ctxt.assume( (spec >>= l_ctxt.weaken(thesis_term)).lift() );
			// fix thesis l ⊢ ∀P. P.[r] ⟹ P.[r]
			Thm refl = lP_ctxt.assume(Pr).intro();
			// fix thesis ⊢ ∀P. P.[r] ⟹ P.[r]
			refl = refl.intro().allE(thesis_term/* or whatever */);
			// ∀thesis. (∀l. (∀P. P.[r] ⟹ P.[l]) ⟹ thesis) ⟹ thesis
			Thm ex = assm.allE(thesis_ctxt.weaken(r_cterm)).impE(refl).intro();
			// l, ∀thesis. ((∀P. P.[r] ⟹ P.[l]) ⟹ thesis) ⟹ thesis
			auto const& [sym,spec_thm] = org_thy.obtain(l,ex,make_spec_name(name),true);
			// deriving intro: ∀P. P.[r] ⟹ P.[l]
			Thm intro_thm = spec_thm << org_thy.term_thm(IMP,REFL).first;
			// deriving elim: ∀P. P.[l] ⟹ P.[r]
			// refl: ∀P. P.[r] ⟹ P.[r]
			Ctxt P_ctxt = org_thy.fork().ctxt();
			P_ctxt.fix(P);
			refl = P_ctxt.assume( P %= P_ctxt.weaken(r_cterm) ).intro();
			Ctxt sur_ctxt = org_thy.fork().ctxt();
			auto x_cterm = sur_ctxt.fix(*avoider(sur_ctxt)("_"));
			sur_ctxt.fix(P);
			CTerm sur = (P %= x_cterm) >>= P %= sur_ctxt.weaken(r_cterm);// P.[x] ⟹ P.[r]
			sur = sur.lift();// ∀x P. P.[x] ⟹ P.[r]
			sur = ASSERTED(sur.capp())->second;// x. ∀P. P.[x] ⟹ P.[r]
			Thm elim_thm = intro_thm.allE(sur).impE(refl);// ∀P. P.[l] ⟹ P.[r]
			// registering
			auto intro_name = name + "_def_intro";
			org_thy.add_thm(intro_name,intro_thm);
			auto elim_name = name + "_def_elim";
			org_thy.add_thm(elim_name,elim_thm);
			PR_MSG << "defined " << _thy.pretty(sym) << " where" << endl <<
				_indent(' ') << "  " << intro_name << ": " << _thy.pretty(intro_thm) << endl <<
				_indent(' ') << "  " << elim_name << ": " << _thy.pretty(elim_thm) << endl;
		} else {
			auto rel = get(TokenType::OPERATOR);
			Term r = get_term();
			skip(".");
			auto [def_name,def_thm] = org_thy.define(Term(rel)(l)(r),name_op);
			PR_MSG << "defined " << def_name << ": " << _thy.pretty(def_thm) << endl;
		}
	}
	void local_thy( Thy loc, function<void()> const& op ) {
		_depth++;
		PROMPT;
		swap(_thy,loc);
		op();
		swap(_thy,loc);
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
			string name = get(Lexer::WORD);
			auto loc = _thy.branch(name,"");
			PR_THY << "creating theory " << name;
			while( auto sym = gets_sym() ) {
				loc.fix(*sym);
				if THY cout << ' ' << loc.pretty_sym(*sym);
			}
			if( skips(".") ) {
			} else {
				if( skips("begin") ) {
					loc.finalize();
				} else {
					skip(":=");
				}
				if THY cout << endl;
				local_thy(loc,[this]{ loop(); });
			}
			PR_MSG << "created theory " << name << endl;
		} else if( skips("context") ) {
			string path = get(Lexer::WORD);
			auto loc = _thy.find_thy(path,reader()).value_or_throw(Error("bad context")(path));
			if( skips(".") ) {
				PR_MSG << "touched " << path << endl;
			} else {
				skip("begin");
				PR_THY << "reopening theory " << loc.source().print_path() << endl;
				local_thy( loc.source(), [this]{ loop(); } );
				PR_MSG << "left " << path << endl;
			}
		} else if( skips("extend") ) {
			auto [pref,name] = get_import_prefix();
			Thy parent = _thy;
			auto src2parent = parent.thy(name,reader());
			auto src = src2parent.source();
			auto loc = parent.branch(src.name(),"");
			vector<CTerm> insts;
			while( auto const& t = gets_term(1000) ) {
				insts.emplace_back(loc.enclose(*t));
			}
			skips(":=");
			PR_THY << "extending theory " << src.print_path() << " into " << loc.print_path() << endl;
			local_thy(loc,[&]{
				auto const& parent2loc = *loc.parent();
				auto src2loc = src2parent.compose(parent2loc);
				_auto_import({},{},src2loc,true,insts);
				add_import(pref,src2loc);
/* not sure this should be automated
				// updating original imports
				auto f = [&]( Opt<string const&> prefix, Import const& sub2org )->Opt<Import>{
					auto sub = sub2org.source();
					auto const& subname = sub.name();
					if( auto const& ext2parent = parent.find_thy(subname,reader()) ) {
						auto ext = ext2parent->source();
						if( ext != loc )// except the theory we are defining
						if( sub.find_import( [&]( Thy const& thy ) { return thy == ext; } ) ) {
							if LOG {
								cout << "already imported ";
								if( prefix ) cout << *prefix << ": ";
								cout << ext.print_path() << endl << _indent(' ');
							}
						} else {
							if MSG {
								cout << "overriding import ";
								if( prefix ) cout << *prefix << ": ";
								cout << sub.print_path() << " by " << ext.print_path() << endl << _indent(' ');
							}
							auto ext2loc = ext2parent->compose(parent2loc);
							_emulate_import(prefix,ext2loc,sub2org);
							return {ext2loc};
						}
					}
					return {};
				};
				for( auto const& sub2org : src.prior_imports() ) {
					if( auto const& o = f({},sub2org) ) {
						_thy.add_prior_import(*o);
					}
				}
				for( auto const& sub2org : src.post_imports() ) {
					if( auto const& o = f({},sub2org) ) {
						_thy.add_post_import(*o);
					}
				}
				for( auto const& [prefix,sub2org] : src2parent.source().imports() ) {
					if( auto const& o = f(prefix,sub2org) ) {
						_thy.add_import(prefix,*o);
					}
				}
*/
				loop();
			});
			PR_MSG << "left " << loc.print_path() << endl;
		} else if ( skips("lemma") || skips("theorem") || skips("proposition") ) {
			auto o = _state();
			if MSG if( o ) {
				auto const& [name,cs,thm] = *o;
				cout << _indent(' ') << "proved " << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
			}
		} else if( skips("note") ) {
			_note();
		} else {
			return false;
		}
		return true;
	}
	Opt<Thm> proof_loop( Thesis& thesis ) {
		for(;;) try {
			if( _stats() ) {
			} else if( skips("obtain") ) {
				_obtain(_thy);
			} else if( skips("define") ) {
				_define(_thy);
			} else if( skips("interpret") ) {
				import(false);
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
			} else if( skips("apply") ) {
				int min, max;
				bool normalize, wide;
				if( skips("+") ) {
					max = 255; normalize = true; wide = true;
				} else {
					max = 0; normalize = false; wide = true;
				}
				do {
					set<Intro> rules;
					while( auto thm = gets_thm() ) {
						rules.emplace(make_rule(*thm));
					}
					min = rules.size();
					if( max == 0 ) max = min;
					thesis.apply(rules,min,max,normalize,wide);
				} while( skips(",") );
				if( !_proof_follows() ) return thesis.discharge_all();
				if MSG print_goals(thesis,"applied goals:\n\t");
			} else if( int mode = skips("simp") ? 1 : skips("rule") ? 2 : 0 ) {
				auto const& [rew_name,ex] = [&]()->Pair<string,string>{
					if( mode == 1 ) return {SIMP,"simplified"};
					return {RULIFY,"rulified"};
				}();
				auto& rew = _thy.rewriter(rew_name);
				auto resolver = Resolver({rew},_out_resolver);
				auto ctrl = _get_rewrite(resolver,_thy,false,true);
				bool more = _proof_follows();
				resolver.rewrites(thesis,{rew_name},ctrl.min,ctrl.max,ctrl.normalize,true,ctrl.pos,ctrl.rel);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, ex + " goals:\n\t" );
			} else if( int mode = skips("unfold") ? 1 : skips("fold") ? 2 : 0 ) {
				for(;;) {
					auto inf = _thy.resolver(_out_resolver);
					auto ctrl = _get_rewrite( inf, _thy, mode == 2, false );
					inf.rewrites(thesis,{},ctrl.min,ctrl.max,ctrl.normalize,true,ctrl.pos,ctrl.rel);
					if( skips(",") ) continue;
					if( skips(".") ) return thesis.discharge_all();
					skip(";");
					if MSG print_goals( thesis, mode == 2 ? "folded goals:\n\t" : "unfolded goals:\n\t" );
					break;
				}
			} else if( skips("rewrite") ) {
				auto inf = _thy.resolver(_out_resolver);
				auto ctrl = _get_rewrite(inf,_thy,false,false);
				bool more = _proof_follows();
				auto const& step = strips_binary(thesis.goal());
				if( !step ) throw Error("\"malformed rewrite step\"")(thesis.goal());
				auto const& [rel,l,r] = *step;
				auto steps = inf.steps(_thy,l,{SIMP},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos,rel);
				thesis.discharge(steps);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals(thesis,"rewritten goals:\n\t");
				
			} else if( int mode = skips("-") ? 1 : skips("show") ? 2 : skips("->") ? 3 : 0 ) {
				auto pat = _get_subgoal( mode == 2 );
				for(;;) {
					if( mode == 3 ) {
						auto resolver = Resolver({_thy.rewriter(RULIFY)}, _out_resolver);
						resolver.rewrites(thesis,{RULIFY},0,255,true,false,{},{});
					}
					auto goal = thesis.has_goal();
					if( !goal ) throw Error("\"unexpected subgoal\"");
					if( auto opt = goal_matches(pat,*goal) ) {
				 		if( *opt ) {
							thesis.discharge(**opt);
						} else {
							PR_MSG << "proof aborted: " << _thy.pretty(*goal) << endl;
						}
						break;
					} else {
						thesis.auto_discharge();
					}
				}
				if MSG print_goals(thesis,"next goals\n\t");
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
				thesis.apply(rule,true);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, "used goals:\n\t" );
			} else if( skips("..") ) {
				auto rel1 = get( TokenType::OPERATOR | TokenType::WORD );
				auto rhs = get_term();
				auto op = strips_binary(thesis.goal());
				if( !op ) throw Error("\"chain proof mismatch\"");
				auto t = _thy.cterm(rhs);
				auto [rel3,s,u] = *op;
				auto claim = _thy.cterm(rel1)(s)(t);
				auto thm = _thy.trans(rel1,rel3).allE(s).allE(t);// s = t ⟹ ∀u. t = u ⟹ s = u
				if( skips(";") ) {
					auto subthy = _thy.scope_temp("#by");
					auto subthesis = Thesis::claim_exact(subthy,claim);
					if MSG {
						cout << _indent(' ') << "chaining: " << subthy.pretty(claim) << endl;
						_depth++;
					} else {
						_depth++;
					}
					PROMPT;
					auto o = _prove(subthesis);
					_depth--;
					if( o ) {
						thesis.apply(Intro::rule(thm.impE(*o)),false);
					}
				} else {
					skip(".");
					thesis.apply( Intro::rule(thm.impE(_thy.prove(claim))), false );
				}
				if MSG print_goals( thesis, "chained goals:\n\t" );
			} else if( skips("oops") ) {
				return {};
			} else if( skips("") ) {
				cerr << location() << ": Unexpected EOF" << endl;
				EXIT(0);
			} else {
				throw Error("\"Unexpected\"")(get());
			}
			PROMPT;
		} catch ( Term const& e ) {
			if( _through_error ) throw e;
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			PROMPT;
		}
	}
	Opt<string> _gets_cons() & {
		auto ret = Opt<string>();
		if( skips("(") ) {
			ret = get();
			skip(")");
		};
		return ret;
	}

	void loop() {
		for(;;) try {
			if( _stats() || _thy_decl() ) {
			} else if( skips("obtain") ) {
				_obtain(_thy);
			} else if( skips("definition") ) {
				_define(_thy);
			} else if( skips("instance") ) {
				import(false);
			} else if( skips("set") ) {
				if( int mode = skips("simp") ? 1 : skips("rule") ? 2 : 0 ) {
					auto& rew = _thy.modify_rewriter( mode == 1 ? SIMP : RULIFY );
					bool def = !skips("?");
					auto rel = get_sym();
					rew.register_rel(rel,def);
					if MSG {
						cout << _indent(' ') << "registered ";
						if( def ) cout << "default ";
						cout << ( mode == 1 ? "simplifier" : "rulifier" ) << " on " << _thy.pretty(rel) << endl;
					}
				} else if( skips("to_true") ) {
					auto thm = get_thm();
					PR_MSG << "registering to_true: " << _thy.pretty(thm) << endl;
					auto& rew = _thy.modify_rewriter(SIMP);
					rew.register_to_true(thm);
				} else if( int mode = skips("letter") ? 1 : skips("symbol") ? 2 : skips("left") ? 3 : skips("right") ? 4 : 0 ) {
					auto [msg,type] = [&]()->Pair<char const*,Lex::CharType>{
						if( mode == 1 ) return {"letters",Lex::Letter};
						if( mode == 2 ) return {"symbols",Lex::MultiOp};
						if( mode == 3 ) return {"left symbols",Lex::LEFTOP};
						return {"right symbols",Lex::RIGHTOP};
					}();
					PR_MSG << "registering " << msg << ": ";
					for(;;) {
						string const& lsym = get(SPECIAL);
						unsigned int l = uint_of_chars(lsym.data());
						if( skips("-") ) {
							string const& rsym = get(SPECIAL);
							unsigned int r = uint_of_chars(rsym.data());
							if MSG cout << lsym  << '-' << rsym << '(' << to_hex(l) << '-' << to_hex(r) << ')';
							lex.register_range(l,r,type);
						} else {
							if MSG cout << lsym;
							lex.register_char(l,type);
						}
						if( !skips(",") ) break;
						if MSG cout << ", ";
					};
					if MSG cout << endl;
				}
				skip(".");
			} else if( skips("prefix") ) {
				string view = get();
				int rlevel = get_int();
				int level = get_int();
				string actual = skips(":=") ? get() : view;
				_make_own_parser();
				_thy.modify_syntax().prefix(view,actual,level,rlevel);
				PR_MSG << "new prefix: " << view << " x := (" << actual << ") x" << endl;
				skip(".");
			} else if( skips("infix") ) {
				string view = get();
				Opt<string> cons;
				if( skips("(") ) {
					cons = {get()};
					skip(")");
				}
				int llevel = get_int();
				int rlevel = get_int();
				int level = get_int();
				string actual = skips(":=") ? get() : view;
				_make_own_parser();
				_thy.modify_syntax().infix(view,actual,level,llevel,rlevel,cons);
				skip(".");
				if MSG {
					cout << _indent(' ') << "new infix: x " << view << " y := ";
					if( cons ) cout << actual << "(x, y)" << endl;
					else cout << '(' << actual << ") x y" << endl;
				}
			} else if( skips("syntax") ) {
				int level = INT_MAX;
				if( skips("[") ) {
					if( skips("level") ) {
						level = get_int();
					} else if( skips("invalid") ) {
						level = Syntax::INVALID;
					}
					skip("]");
				}
				if( skips("_") ) {// _ !
					auto post = get();
					if( skips(":=") ) {
						auto actual = get_sym();
						_thy.modify_syntax().postfix(post,actual,level);
					} else {
						_thy.modify_syntax().postfix(post,post,level);
					}
				} else {
					auto opener = get();
					if( skips("_") ) {
						if( skips(".") ) {// {_. _}
							skip("_");
							auto closer = get();
							skip(":=");
							auto actual = get_sym();
							_thy.modify_syntax().compr(opener,closer,actual,level);
							PR_MSG << "comprehension: " << opener << "x. y" << closer << " := " << _thy.pretty(actual) << " (x. y)" << endl;
						} else {
							auto next = get();
							if( skips("_") ) {
								skip(".");
								skip("_");
								if( skips(":=") ) {// ∀_ < _. _
									auto actual = get_sym();
									auto cons = _gets_cons();
									_thy.modify_syntax().binder_mid(opener,next,actual,cons);
									if MSG {
										cout << _indent(' ') << "binder middle " << opener << " x " << next << " y. z := " << actual;
										if( cons ) {
											cout << "(y " << *cons << " (x. z))" << endl;
										} else {
											cout << " y (x. z)" << endl;
										}
									}
								} else {// {_ < _. _}
									auto closer = get();
									skip(":=");
									auto actual = get_sym();
									auto cons = _gets_cons();
									_thy.modify_syntax().bcompr(opener,next,closer,actual,cons,level);
									if MSG {
										cout << _indent(' ') << "bounded comprehension: " << opener << "x " << next << " y. z" << closer << " := " << _thy.pretty(actual);
										if( cons ) {
											cout << "(y " << *cons << " (x. z))" << endl;
										} else {
											cout << " y (x. z)" << endl;
										}
									}
								}
							} else {// {_}
								skip(":=");
								auto actual = get_sym();
								_thy.modify_syntax().singleton_compr(opener,next,actual,level);
								PR_MSG << "singleton comprehension: " << opener << " x " << next << " := " << _thy.pretty(actual) << " x" << endl;
							}
						}
					} else {// {}
						auto closer = get();
						skip(":=");
						auto actual = get_sym();
						_thy.modify_syntax().empty_compr(opener,closer,actual,level);
						PR_MSG << "empty comprehension: " << opener << ' ' << closer << " := " << _thy.pretty(actual) << endl;
					}
				}
				skip(".");
			} else if( skips("binder") ) {
				string sym = get();
				int llevel = get_int();
				int rlevel = get_int();
				_make_own_parser();
				_thy.modify_syntax().binder(sym,llevel,rlevel);
				PR_MSG << "new binder: " << sym << endl;
				skip(".");
			} else if( skips("end") || skips("") ) {
				return;
			} else if( !_thy.finalized() ) {
				if( skips("fix") ) {
					if CTXT cout << _indent(' ') << "fixing";
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
					if CTXT cout << _indent(' ') << "assumed " << _print_name_status(name,cs) << _thy.pretty(assm) << ". " << endl;
					skip(".");
				} else if( skips("import") ) {
					import(true);
				} else if( skips("begin") ) {
					_thy.finalize();
					PR_MSG << "finalized" << endl;
				} else {
					throw Error("\"unexpected\"")(get());
				}
			} else {
				throw Error("\"unexpected\"")(get());
			}
			PROMPT;
		} catch ( Term const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			PROMPT;
		}
	}
	void _obtain( Thy& org_thy ) {
		auto t = get_term(1000);
		auto sym = t.sym();
		if( !sym ) throw Error("\"expected a symbol\"")(t);
		vector<CTerm> props;
		vector<tuple<Opt<string>,ClaimStatus,Thm>> prop_thms;
		Thy thesis_thy = _thy.branch();
		CTerm var = thesis_thy.fix("_thesis");
		Thy goal_thy = thesis_thy.branch();
		goal_thy.fix(*sym);
		auto props_thy = org_thy.branch();
		props_thy.fix(*sym);
		PR_MSG << "obtaining " << *sym;
		if( skips("where") ) {
			if MSG cout << " where" << endl;
			for(;;) {
				auto [name,cs] = _get_name_status();
				auto assm = _get_assm(props_thy);
				Thm thm = props_thy.assume(assm);
				add_claim(props_thy,name,cs,thm);
				prop_thms.emplace_back(name,cs,thm);
				props.push_back(goal_thy.cterm(assm));
				PR_MSG << "  " << _print_name_status(name,cs) << _thy.pretty(thm) << endl;
				if( !skips(",") ) break;
			}
		}
		CTerm goal = goal_thy.weaken(var);
		for( auto& prop : ranges::reverse_view(props) ) {
			goal = prop >>= goal;
		}
		goal = goal.lift() >>= var;
		goal = goal.lift();
		auto thesis = Thesis::claim_exact(_thy,goal);
		_depth++;
		skip(";");
		PROMPT;
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
			PR_MSG << "obtained " << *sym << endl;
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

struct ParentInfo {
	string name;
	filesystem::path filepath;
	filesystem::path dirpath;
};
void run( istream& is, string const& name, string const& filepath, bool exit_on_error, unsigned short out, filesystem::path const& cmddir, filesystem::path locdir, bool print_on_end ) try {
	auto rootdir = string(cmddir);
	auto root = Thy("",rootdir);// the empty root theory, linked to the root directory of NLT
	auto lex = Lex();
	init_lex(lex);
	init_syntax(root.modify_syntax());
	vector<ParentInfo> parents;
	for(;;) {
		auto parent_nl = filesystem::path( locdir + ".nl" );
		if( !filesystem::exists(parent_nl) ) break;
		parents.emplace_back(locdir.filename(),parent_nl,locdir);
		locdir = locdir.parent_path();
	}
	Thy thy = filesystem::equivalent(rootdir,locdir) ? root : root.branch((string)locdir.stem(),locdir);
	auto prover = Prover(thy,is,filepath,lex,exit_on_error,out,FLAG_SYS,0);
	for( auto& parent : views::reverse(parents) ) {
		thy = thy.branch((string)parent.name,parent.dirpath);
		thy.add_import(parent.name,thy.self(),true,false,true);
		auto fis = ifstream(parent.filepath);
		prover.reader()(thy,fis,parent.filepath);
	}
	thy = thy.branch(name,name);
	prover.thy() = thy;
	prover.loop();
	if( print_on_end ) {
		cout << thy.pretty() << endl;
	} else {
		cout << "bye!" << endl;
	}
} catch( Term const& e ) {
	EXIT(-1);
}

int main(int argc, char* argv[]) {
	bool exit_on_error = true;
	bool print_on_exit = true;
	auto cmd = filesystem::path(argv[0]);
	auto cmddir = cmd.parent_path();
	auto verb = FLAGS_MIN;
	int i = 1;
	for(;;) {
		if( i == argc ) {
			run( cin, "#stdin", "#stdin", false, FLAGS_DEFAULT | FLAG_PROMPT, cmddir, filesystem::current_path(), false );
			return 0;
		}
		string arg = argv[i];
		if( arg.starts_with('-') ) {
			auto opt = arg.substr(1);
			if( opt == "i" ) {
				verb = FLAGS_DEFAULT;
				print_on_exit = false;
			} else if( opt == "e" ) {
				exit_on_error = false;
			} else {
				cerr << "unexpected option " << arg << endl;
				return -1;
			}
			i++;
			continue;
		}
		auto file = filesystem::path(arg);
		if( file.extension() != ".nl" ) {
			cerr << "unsupported file type: " << arg << endl;
			EXIT(-1);
		}
		auto parent = file.parent_path();
		auto locdir = parent.empty() ? filesystem::current_path() : filesystem::absolute(parent);
		auto fin = fstream(file);
		run(fin,file.stem(),file,exit_on_error,verb,cmddir,locdir,print_on_exit);
		break;
	}
	return 0;
}

