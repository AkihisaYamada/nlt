#include<fstream>
#include<filesystem>
#include<ranges>
#include"inference.hpp"
#include"parser.hpp"

#define FLAG_ERR (1 << 0)
#define FLAG_SYS (1 << 1)
#define FLAG_STA (1 << 2)
#define FLAG_CTXT (1 << 3)
#define FLAG_THY (1 << 4)
#define FLAG_MSG (1 << 5)
#define FLAG_LOG (1 << 6)
#define FLAG_PRF (1 << 7)

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
#define PRF ( _out & FLAG_PRF )

using namespace std;

string const RULIFY = "#rulify";
string const RULIFY_CONG = "#rcong";

struct ClaimStatus {
	struct Ternary {
		bool self, weak;
		operator bool() const { return self; }
		void operator=( bool b ) { self = b; }
	};
	Ternary intro = {false,false}, cong = {false,false};
	bool elim = false, dual = false, trans = false, unfold = false, fold = false, inflated = false, rulify = false, rulify_cong = false, followable = true;
	unsigned char after = 0;
	unsigned char prems = 255;
	bool strip_all = true;
	static ClaimStatus const INFLATED;
};
inline ClaimStatus const ClaimStatus::INFLATED = {
	.intro = {true,false},
	.inflated = true,
};

ostream& operator<<( ostream& os, ClaimStatus && cs ) = delete;

ostream& operator<<( ostream& os, ClaimStatus const& cs ) {
	auto _print_cs_mod = [&]{
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
		os << post;
	}; 
	if( cs.intro ) {
		os << "#intro";
		if( cs.intro.weak ) os << '?';
		_print_cs_mod();
	}
	if( cs.elim ) {
		os << "#elim";
	}
	if( cs.dual ) {
		os << "#dual";
	}
	if( cs.unfold ) {
		os << "#simp";
		_print_cs_mod();
	}
	if( cs.fold ) {
		os << "#fold";
	}
	if( cs.cong ) {
		os << "#cong";
		if( cs.cong.weak ) os << '?';
	}
	return os << ": ";
}

Pair<fstream,string> file_of_thy( string_view const& dir, string_view const& name ) {
	auto path = string(dir);
	path+=name;
	path+=".nl";
	return {fstream(path),std::move(path)};
}

void init_lex( Lex& lex ) {
	lex.register_char('!',Lex::MultiOp);
	lex.register_range('#','&',Lex::MultiOp);
	lex.register_char('\'',Lex::Letter);
	lex.register_range('*','+',Lex::MultiOp);
	lex.register_char(',',Lex::SingleOp);
	lex.register_char('-',Lex::MultiOp);
	lex.register_char('/',Lex::MultiOp);
	lex.register_char(':',Lex::MultiOp);
	lex.register_char(';',Lex::SingleOp);
	lex.register_range('<','@',Lex::MultiOp);
	lex.register_char('\\',Lex::MultiOp);
	lex.register_char('^',Lex::MultiOp);
	lex.register_char('`',Lex::MultiOp);
	lex.register_char('|',Lex::MultiOp);
	lex.register_char('~',Lex::MultiOp);
}
void init_syntax( Syntax& syntax ) {
	syntax.infix(":",":",50,51,50,{});
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
	Prover( Thy const& thy, istream& is, std::filesystem::path const& filename, Lex& lex, bool through_error, char out, char out_load, unsigned char depth ) :
		_depth(depth),
		_thy(thy),
		lex(lex),
		Parser(is,(string)filename,lex),
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
		return _gets_thm(_thy);
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
	Opt<Thm> _gets_thm( Thy& thy ) {
		auto const& opt = gets_thm_name();
		if( !opt ) {
			return {};
		}
		Thm ret = thy.thm(*opt);
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
					auto reorder_prems = vector<Sum<Thm,pair<bool,size_t>>>();
					auto args = vector<Thm>();
					auto head_prems = vector<CTerm>();
					auto tail_prems = vector<CTerm>();
					for(;;) {
						strip_thm = strip_all(strip_thm,var_ctxt).first;
						auto imp = strip_thm.cbinary(IMP);
						if( !imp ) break;
						int mode;
						if( skips("_") ) {// assume the premise later
							mode = 1;
						} else if( skips("<") ) {// assume before
							mode = 2;
						} else if( auto const& arg = _gets_thm(loc) ) {// unify with the argument
							mode = 3;
							args.emplace_back(*arg);
						} else {
							break;
						}
						strip_thm = strip_thm.impE(strip_ctxt.assume(imp->first));
						auto reorder_prem = reorder_ctxt.weaken(imp->first.lift());
						switch( mode ) {
						case 1:
							reorder_prems.emplace_back(pair{false,tail_prems.size()});
							tail_prems.emplace_back(reorder_prem);
							break;
						case 2:
							reorder_prems.emplace_back(pair{true,head_prems.size()});
							head_prems.emplace_back(reorder_prem);
							break;
						case 3:
							reorder_prems.emplace_back(reorder_ctxt.assume(reorder_prem));
							break;
						} 
					}
					// forming reordered theorem
					auto head_assms = vector<Thm>();
					for( auto const& head : head_prems ) {
						head_assms.emplace_back( reorder_ctxt.assume(head) );
					}
					auto tail_assms = vector<Thm>();
					for( auto const& tail : tail_prems ) {
						tail_assms.emplace_back( reorder_ctxt.assume(tail) );
					}
					auto reorder = Intp::make(strip_ctxt,var_ctxt).compose(reorder_intp);
					for( auto const& prem : reorder_prems ) {
						if( auto thm = prem.ref<Thm>() ) {
							reorder.discharge(*thm);
						} else {
							auto [head,ind] = *prem.ref<1>();
							if( head ) {
								reorder.discharge(head_assms[ind]);
							} else {
								reorder.discharge(tail_assms[ind]);
							}
						}
					}
					// obtain the theorem with premises reordered, and then variables quantified 
					tmp = strip_thm.subst(reorder).intro().intro();
					// in particular, premises which will be unified come in front
					for( auto const& arg : args ) {
						tmp = tmp << arg;
					}
				} else if( skips("THEN") ) {
					auto sub = loc.branch();
					auto tmp2 = sub.weaken(tmp); // φ ⟹... ψ
					auto thm = _get_thm(sub);// ψ ⟹ χ
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
					auto ctrl = _get_rewrite(resolver,loc,mode==2);
					tmp = resolver.rewrites(loc,tmp,{},ctrl.min,ctrl.max,ctrl.normalize,ctrl.pos);
				} else if( skips("simp") ) {
					auto const& rew = loc.rewriter(SIMP);
					auto resolver = Resolver(rew,_out_resolver);
					while( auto thm = _gets_thm(loc) ) {
						rew.add_rewrite_rule(resolver.rules,*thm,false);
					}
					tmp = resolver.rewrites(loc,tmp,{SIMP},1,255,true,{});
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
	function<ostream&(ostream&)> _indent( char c = '>' ) const & {
		return [c,this]( ostream& os )->ostream& {
			for( int i = 0; i <= _depth; i++ ) {
				os << c;
			}
			return os << ' ' << flush;
		};
	}
	Opt<ClaimStatus> gets_claim_status() {
		ClaimStatus cs;
		if( skips("!") ) {
			cs.intro = {true,false};
			cs.inflated = true;
		} else if( skips("?") ) {
			cs.intro = {true,true};
			cs.inflated = true;
		} else if( skips("#") ) {
			do {
				if( skips("intro") ) {
					cs.intro = {true,skips("?")};
				} else if( skips("cong") ) {
					cs.cong = {true,skips("?")};
				} else if( skips("rule" ) ) {
					cs.rulify = true;
				} else if( skips("rule_cong") ) {
					cs.rulify_cong = true;
				} else if( skips("elim") ) {
					cs.elim = true;
				} else if( skips("dual") ) {
					cs.dual = true;
				} else if( skips("trans") ) {
					cs.trans = true;
				} else if( skips("simp") ) {
					cs.unfold = true;
				} else if( skips("fold") ) {
					cs.fold = true;
				} else {
					throw Error("\"unknown rule\"")(peek_token());
				}
				if( skips("[") ) {
					do {
						if( skips("after") ) {
							cs.after = get_int();
						} else if( skips("prems") ) {
							cs.prems = get_int();
						} else if( skips("no_expand") ) {
							cs.strip_all = false;
						} else break;
					} while( skips(",") );
					skip("]");
				}
			} while( skips("#") );
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
					info = {Elim::rule( thm, cs->after-1, cs->intro.weak ? '?' : '!' )};
					loc.add_thm(INF,thm,info);
				} else {
					info = {Intro::imp(thm,cs->prems,cs->strip_all)};
					add_intro(loc,thm,*info.ref<Intro>(),!cs->intro.weak);
				}
			}
			if( cs->cong ) {
				if( cs->cong.weak ) {
					loc.modify_rewriter(SIMP).register_fallback(thm);
				} else {
					loc.modify_rewriter(SIMP).register_cong(thm);
				}
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
			if( cs->trans ) {
				loc.register_trans(thm);
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
				if CTXT {
					auto disp = [&]( ostream& os )->ostream&{ return os << "fixed " << _thy.pretty_sym(sym) << endl; };
					if( MSG ) {
						cout << disp << _indent(' ');
					} else {
						cout << _indent(' ') << disp;
					}
				}
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
			if MSG cout << "transferred " << disp << _indent(' ');
			return;
		}
		if( prefix ) {
			assm_name = *prefix + '.' + assm_name;
			if( auto const& o = _thy.find_thm(assm_name,exact(assm)) ) {
				intp.discharge(*o);
				if MSG cout << "transferred " << disp << _indent(' ');
				return;
			}
		}
		if( change ) {
			Thm ret = org_thy.add_assm(assm_name,assm);
			intp.discharge(ret);
			if CTXT {
				if( MSG ) {
					cout << "admitted " << disp << _indent(' ');
				} else {
					cout << _indent(' ') << "admitted " << disp;
				}
			}
			return;
		}
		if MSG cout << "blasting " << disp << _indent(' ');
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
				if MSG {
					cout << "blasting " << name << ": " << _thy.pretty(stmt) << endl << _indent(' ');
				}
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
		return [&]( Thy& thy, istream& fis, std::filesystem::path const& filepath ){
			if SYS {
				if( !MSG ) cout << _indent(' ');
				cout << "loading " << filepath << endl;
			}
			Prover(thy,fis,filepath,lex,true,_out_load,_out_load,_depth+1).loop();
			if ( SYS && _out_load & (FLAG_CTXT|FLAG_THY) ) {
				auto pr = [&](ostream&os)->ostream&{ return os << "loaded " << filepath << endl; };
				if( !MSG ) cout << _indent(' ') << pr;
				else cout << pr << _indent(' ');
			}
		};
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
		string name;
		Opt<string> default_prefix = {};
		Opt<string> optional_prefix = {};
		Opt<string> forced_prefix = {};
		bool canonical_prefix = false;
		bool rec = false;
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
	ImportPrefix get_import_prefix() {
		ImportPrefix ret;
		if( skips("?") ) {// weak unnamed import
			ret.name = get_thm_name();
			ret.default_prefix = {NONREC_IMPORT};
			ret.canonical_prefix = true;
		} else if( skips("!") ) {// expansive unnamed import
			ret.name = get_thy_name();
			ret.default_prefix = {""};
			ret.canonical_prefix = true;
			ret.rec = true;
		} else if( skips(":") ) {// canonically qualified import
			ret.name = get_thy_name();
			ret.canonical_prefix = true;
		} else {
			string str1 = get_thy_name();
			if( skips(":") ) {// qualified import
				ret.name = get();
				ret.forced_prefix = {str1};
			} else if( skips("!") ) {// qualified recursive
				ret.name = get();
				ret.forced_prefix = {str1};
				ret.rec = true;
			} else if( skips("?") ) {// optionally qualified
				ret.name = get();
				ret.default_prefix = {""};
				ret.optional_prefix = {str1};
			} else {// unqualified
				ret.name = str1;
				ret.default_prefix = {""};
				ret.canonical_prefix = true;
				ret.rec = false;
			}
		}
		return std::move(ret);
	};
	void add_import( ImportPrefix const& pref, Import const& import ) {
		auto src = import.source();
		_update_parent(src);// in case of interpreting a child.
		if( pref.forced_prefix ) {
			_thy.add_import(*pref.forced_prefix,import,pref.rec,false);
		}
		if( pref.default_prefix ) {
			_thy.add_import(*pref.default_prefix,import,pref.rec,pref.rec);
			if( *pref.default_prefix == "" && _no_syntax ) {// TODO: make elegant
				_no_syntax = false;
				_thy.modify_syntax() = import.source().syntax();
			}
		}
		if( pref.optional_prefix ) {
			_thy.add_import(*pref.optional_prefix,import,pref.rec,false);
		}
		if( pref.canonical_prefix ) {
			_thy.add_import(import.source().name(),import,pref.rec,false);
		}
	};
	void import( bool change ) {
		ImportPrefix pref = get_import_prefix();
		auto intp = _thy.thy(pref.name,reader());
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
			if MSG cout << (change ? "importing " : "interpreting ") << pref << path << endl;
			_depth++;
			success = _import_loop(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
			_depth--;
			if( success ) {
				add_import(pref,intp);
				if THY {
					if( !MSG ) cout << _indent(' ');
					cout << ( change ? "imported " : "interpreted " ) << pref << path << endl;
				}
			}
		} else if( skips(",") ) {
			_auto_import(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
			add_import(pref,intp);
			if THY cout << ( change ? "imported " : "interpreted " ) << pref << intp.source().print_path() << endl;
			return import(change);
		} else {
			skip(".");
			_auto_import(pref.forced_prefix,pref.forced_prefix,intp,change,insts);
			if THY cout << ( change ? "imported " : "interpreted " ) << pref << intp.source().print_path() << endl;
			add_import(pref,intp);
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
		size_t n = _print_import_goal(intp,i,"\t");
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
		bool show = skips("show");
		if( show ) {
			ret.name = gets( Tokenizer::WORD | Tokenizer::NUMBER );
			ret.cs = gets_claim_status();
			if( !ret.cs ) skip(":");
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
					auto name = gets( Tokenizer::WORD | Tokenizer::NUMBER );
					auto const& cs = gets_claim_status();
					auto assm = cs ? gets_term() : skips(":") ? Opt<Term>{get_term()} : Opt<Term>();
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
		auto css = vector<Pair<Opt<string>,Opt<ClaimStatus>>>();
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
					while( auto const& v = loc.fixed(prev) ) {
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
			} else {
				assert(false);
			}
		}
		if( pat.concl ) {
			size_t prev = loc.revision();
			auto concl = loc.enclose(*pat.concl);
			while( auto const& v = loc.fixed(prev) ) {
				auto all = loc_goal.cunary(ALL);
				if( !all || !all->bind() ) return {};
				loc_goal = all->inst(loc.cterm(*v));
				prev++;
			}
			if( loc_goal != concl ) return {};
		}
		if( pat.proof ) {
			if MSG {
				cout << "showing ";
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
							if( _print_import_goal(intp,0,"next ") == 0 ) {
								cout << "QED" << endl;
							}
						}
					} else {
						if MSG cout << "aborted " << assume->second << ": " << _thy.pretty(assume->first) << endl;
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
		if MSG {
			cout << _indent(' ');
			_print_import_goals(intp);
		}
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
					if MSG cout << "instantiated " << x << " := " << _thy.pretty(t) << endl;
				}
			} else if( skips("-") ) {
				auto pat = _get_subgoal();
				_discharge( [&]( CTerm const& assm ){ return goal_matches(pat,assm); }, intp, org_thy, thm_prefix, sym_prefix, change, inst_it, inst_end );
			} else if( skips("->") ) {
				auto pat = _get_subgoal();
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
				exit(0);
			} else {
				throw Error("\"Unexpected\"")(get());
			}
		} catch( Term const& e ) {
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if( _through_error ) throw THROUGH;
			if MSG cout << _indent();
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
				resolver.inflate(_thy,*thm);
				add_intro(_thy,*thm,true);
			}
			while( auto cs = gets_claim_status() ) {
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
		if( skips("proof") ) return FLAGS_DEFAULT | FLAG_PRF;
		skips("default");
		return FLAGS_DEFAULT;
	}
	bool _stats() {
		if( skips("ctxt") ) {
			auto const indent_endl = [this]( ostream& os )->ostream&{ return os << endl << _indent(' '); };
			auto thy = _thy;
			if( !skips(".") ) {
				string name = get();
				thy = thy.thy(name,reader()).source();
				skip(".");
			}
			cout << thy.pretty(indent_endl) << endl;
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
				if MSG cout << "set print ctxt_id" << endl;
			} else if( skips("load") ) {
				_out_load = get_print_level();
				if MSG cout << "set print load level " << _out_load << endl;
			} else if( skips("prover") ) {
				_out_resolver = gets_int().value_or(5);
				if MSG cout << "set print prover level " << endl;
			} else {
				_out = get_print_level();
				if MSG cout << "set print level " << endl;
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
				if MSG {
					cout << "\t";
					if( cs ) cout << *cs;
					cout << _thy.pretty(*o) << endl;
				}
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
	Pair<Opt<string>,Opt<ClaimStatus>> _get_name_status() {
		Pair<Opt<string>,Opt<ClaimStatus>> ret;
		ret.first = gets( Tokenizer::WORD | Tokenizer::NUMBER );
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
		Term eq = get_term();
		skip(".");
		auto [def_name,def_thm] = org_thy.define(eq,name_op);
		if MSG cout << "defined " << def_name << ": " << _thy.pretty(def_thm) << endl;
	}
	void local_thy( Thy loc, bool finalized, function<void()> const& op ) {
		_depth++;
		if MSG cout << _indent();
		swap(_thy,loc);
		swap(_final,finalized);
		op();
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
			if THY {
				if( !MSG ) cout << _indent(' ');
				cout << "creating theory " << name;
			}
			while( auto sym = gets_sym() ) {
				loc.fix(*sym);
				if THY cout << ' ' << loc.pretty_sym(*sym);
			}
			if( skips(".") ) {
			} else {
				bool finalized;
				if( skips("begin") ) {
					finalized = true;
				} else {
					skip(":=");
					finalized = false;
				}
				if THY cout << endl;
				local_thy(loc,finalized,[this]{ loop(); });
			}
			if MSG cout << "created theory " << name << endl;
		} else if( skips("context") ) {
			string path = get(Lexer::WORD);
			auto loc = _thy.find_thy(path,reader()).value_or_throw(Error("bad context")(path));
			if( skips(".") ) {
				if MSG cout << "touched " << path << endl;
			} else {
				skip("begin");
				if THY {
					if( !MSG ) cout << _indent(' ');
					cout << "reopening theory " << loc.source().print_path() << endl;
				}
				local_thy( loc.source(), true, [this]{ loop(); } );
				if MSG cout << "left " << path << endl;
			}
		} else if( skips("extend") ) {
			auto pref = get_import_prefix();
			Thy parent = _thy;
			auto src2parent = parent.thy(pref.name,reader());
			auto src = src2parent.source();
			auto loc = parent.branch(src.name(),"");
			vector<CTerm> insts;
			while( auto const& t = gets_term(1000) ) {
				insts.emplace_back(loc.enclose(*t));
			}
			skip("begin");
			if THY {
				if( !MSG ) cout << _indent(' ');
				cout << "extending theory " << src.print_path()
					<< " into " << loc.print_path() << endl;
			}
			local_thy(loc,true,[&]{
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
			if MSG cout << "left " << loc.print_path() << endl;
		} else if( skips("namespace") ) {
			auto name = get(Lexer::WORD);
			skip("begin");
			if THY {
				if( !MSG ) cout << _indent(' ');
				cout << "creating namespace " << name << endl;
			}
			auto loc = _thy.scope(name);
			local_thy(loc,_final,[this]{ loop(); });
			if MSG cout << "created namespace " << name << endl;
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
			} else if( int mode = skips("simp") ? 1 : skips("rule") ? 2 : 0 ) {
				auto const& [rew_name,ex] = [&]()->Pair<string,string>{
					if( mode == 1 ) return {SIMP,"simplified"};
					return {RULIFY,"rulified"};
				}();
				auto& rew = _thy.rewriter(rew_name);
				auto resolver = Resolver({rew}, _out_resolver);
				while( auto thm = gets_thm() ) {
					rew.add_rewrite_rule(resolver.rules,*thm,false);
				}
				bool more = _proof_follows();
				resolver.rewrites(thesis,{rew_name},1,255,true,true,{},{});
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, ex + " goals:\n\t" );
			} else if( int mode = skips("unfold") ? 1 : skips("fold") ? 2 : 0 ) {
				auto inf = _thy.resolver(_out_resolver);
				auto ctrl = _get_rewrite( inf, _thy, mode == 2 );
				bool more = _proof_follows();
				inf.rewrites(thesis,{},ctrl.min,ctrl.max,ctrl.normalize,true,ctrl.pos,ctrl.rel);
				if( !more ) return thesis.discharge_all();
				if MSG print_goals( thesis, mode == 2 ? "folded goals:\n\t" : "unfolded goals:\n\t" );
			} else if( int mode = skips("-") ? 1 : skips("->") ? 2 : 0 ) {
				auto pat = _get_subgoal();
				for(;;) {
					if( mode == 2 ) {
						auto resolver = Resolver({_thy.rewriter(RULIFY)}, _out_resolver);
						resolver.rewrites(thesis,{RULIFY},0,255,true,false,{},{});
					}
					auto goal = thesis.has_goal();
					if( !goal ) throw Error("\"unexpected subgoal\"");
					if( auto opt = goal_matches(pat,*goal) ) {
				 		if( *opt ) {
							thesis.discharge(**opt);
						} else {
							if MSG cout << "proof aborted: " << _thy.pretty(*goal) << endl;
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
			} else if( skips("...") ) {
				auto rel = get( TokenType::OPERATOR | TokenType::WORD );
				auto t = get_term();
				auto goal = thesis.goal();
				auto op = goal.cbinary(rel);
				if( !op ) throw Error("\"transitive proof mismatch\"");
				auto lhs = op->first;
				auto rhs = _thy.cterm(t);
				auto claim = _thy.cterm(rel)(lhs)(rhs);
				auto thm = _thy.trans(rel).allE(lhs).allE(rhs);// s = t ⟹ ∀u. t = u ⟹ s = u
				if( skips(";") ) {
					auto subthesis = Thesis::claim_exact(_thy,claim);
					_depth++;
					if MSG cout << _indent();
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
				exit(0);
			} else {
				throw Error("\"Unexpected\"")(get());
			}
			if MSG cout << _indent();
		} catch ( Term const& e ) {
			if( _through_error ) throw e;
			cerr << "ERROR: " << location() << ": " << _thy.pretty(e) << endl;
			if MSG cout << _indent();
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
			if( _stats() || _thy_decl() || _shared_decl() ) {
			} else if( skips("set") ) {
				if( int mode = skips("simp") ? 1 : skips("rule") ? 2 : 0 ) {
					auto& rew = _thy.modify_rewriter( mode == 1 ? SIMP : RULIFY );
					bool def = skips("!");
					Thm imp = get_thm();
					Thm revimp = get_thm();
					Thm refl = get_thm();
					if MSG cout << "registering " << ( mode == 1 ? "simplifier" : "rulifier" ) <<
						":\n\timp: " << _thy.pretty(imp) <<
						"\n\trev: " <<  _thy.pretty(revimp) <<
						"\n\trefl: " << _thy.pretty(refl);
					rew.register_refl(refl,def);
					rew.register_imp(imp,true);
					rew.register_imp(revimp,false);
					if MSG cout << endl;
				} else if( skips("to_true") ) {
					auto thm = get_thm();
					if MSG cout << "registering to_true: " << _thy.pretty(thm) << endl;
					auto& rew = _thy.modify_rewriter(SIMP);
					rew.register_to_true(thm);
				} else if( int mode = skips("letter") ? 1 : skips("symbol") ? 2 : skips("solo") ? 3 : 0 ) {
					auto [msg,type] = [&]()->Pair<char const*,Lex::CharType>{
						if( mode == 1 ) return {"letters",Lex::Letter};
						if( mode == 2 ) return {"symbols",Lex::MultiOp};
						return {"solo symbols",Lex::SingleOp};
					}();
					if MSG cout << "registering " << msg << ": ";
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
				if MSG cout << "new prefix: " << view << " x := (" << actual << ") x" << endl;
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
					cout << "new infix: x " << view << " y := ";
					if( cons ) cout << actual << "(x, y)" << endl;
					else cout << '(' << actual << ") x y" << endl;
				}
			} else if( skips("syntax") ) {
				int level = gets_int().value_or(INT_MAX);
				auto opener = get();
				if( skips("_") ) {
					if( skips(".") ) {// {_. _}
						skip("_");
						auto closer = get();
						skip(":=");
						auto actual = get_sym();
						_thy.modify_syntax().compr(opener,closer,actual,level);
						if MSG cout << "comprehension: " << opener << "x. y" << closer << " := " << _thy.pretty(actual) << " (x. y)" << endl;
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
									cout << "binder middle " << opener << " x " << next << " y. z := " << actual;
									if( cons ) {
										cout << "(y " << *cons << " z)" << endl;
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
									cout << "bounded comprehension: " << opener << "x " << next << " y. z" << closer << " := " << _thy.pretty(actual);
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
							if MSG cout << "singleton comprehension: " << opener << " x " << next << " := " << _thy.pretty(actual) << " x" << endl;
						}
					}
				} else {// {}
					auto closer = get();
					skip(":=");
					auto actual = get_sym();
					_thy.modify_syntax().empty_compr(opener,closer,actual,level);
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
		goal = goal.lift() >>= var;
		goal = goal.lift();
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

struct ParentInfo {
	string name;
	filesystem::path filepath;
	filesystem::path dirpath;
};
void run( istream& is, string const& name, string const& filepath, bool exit_on_error, char out, filesystem::path const& cmddir, filesystem::path locdir, bool print_on_end ) try {
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
		thy.add_import(parent.name,thy.self(),true,false);
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
	exit(-1);
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
			run( cin, "#stdin", "#stdin", false, FLAGS_DEFAULT, cmddir, filesystem::current_path(), false );
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
			exit(-1);
		}
		auto parent = file.parent_path();
		auto locdir = parent.empty() ? filesystem::current_path() : filesystem::absolute(parent);
		auto fin = fstream(file);
		run(fin,file.stem(),file,exit_on_error,verb,cmddir,locdir,print_on_exit);
		break;
	}
	return 0;
}

