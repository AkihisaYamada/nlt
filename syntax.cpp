#include "syntax.hpp"

using namespace std;

Syntax SYNTAX;

Syntax::Syntax() {
	infix("⟹","⟹",0,1,0,{});
	binder("∀",0,0);
	infix(".",".",-1,-1,-2,{});// Dot cannot be an symbol
	postfix(")","#rparen",INVALID);
}

ostream& Syntax::pretty_sym( ostream& os, string_view const& sym ) const & {
	if( _prefixes.contains(sym) || _binders.contains(sym) || _pretty_of.contains(sym) ) {
		return os << '(' << sym << ')';
	}
	if( auto const& x = _pretty_of.finds_value(sym) ) {
		if( auto y = x->ref<Empty>() ) {
			return os << y->opener << y->closer;
		}
	}
	return os << sym;
}
ostream& _pretty_num( Syntax const& syn, ostream& os, unsigned char e, unsigned int num, Term const& inner ) {
	if( auto const& app = inner.app() ) {
		auto const& [fun,arg] = *app;
		if( auto const& sym = fun.sym() ) {
			if( fun == Syntax::BIT0 ) return _pretty_num( syn, os, e+1, num, arg );
			if( fun == Syntax::BIT1 ) return _pretty_num( syn, os, e+1, num | (1<<e), arg );
		}
	} else if( inner.sym().contains("1") ) {
		return os << (num | (1<<e));
	}
	// ill-formed number
	for( unsigned char i = 0; i < e; i++ ){
		os << '(' << ( num & 1 ? Syntax::BIT1 : Syntax::BIT0 ) << ' ';
		num >>= 1;
	}
	os << syn.pretty(inner,1000);
	for( ; e != 0; e-- ) os << ')';
	return os;
}
ostream& Syntax::pretty( ostream& os, Term const& term, int level ) const & {
	if( auto const& sym = term.sym() ) {
		return pretty_sym(os,*sym);
	} else if( auto const& app = term.app() ) {
		auto const& [fun,arg] = *app;
		if( auto const& sym = fun.sym() ) {// unary application
			if( *sym == BIT0 ) {
				return _pretty_num(*this,os,1,0,arg);
			} else if( *sym == BIT1 ) {
				return _pretty_num(*this,os,1,1,arg);
			} else if( auto const& op = _binders.finds_value(*sym) ) {// ∀x. s
				if( auto const& abs = arg.bind() ) {
					if( level > op->llevel ) os << '(';
					os << *sym << ' ' << pretty_sym(abs->first);
					Term cur = abs->second;
					while( auto abs2 = cur.binder(*sym) ) {
						os << ' ' << pretty_sym(abs2->first);
						cur = abs2->second;
					}
					os << ". " << pretty(cur,op->rlevel);
					if( level > op->llevel ) os << ')';
					return os;
				}
			} else if( auto const& sum = _pretty_of.finds_value(*sym) ) {
				if( auto const& x = sum->ref<Unary>() ) {// f s
					auto const& [postfix,view] = *x;
					if( postfix ) {// s!
						auto op = *ASSERTED(_postfixes.finds_value(view));
						if( level > op.level ) os << '(';
						os << pretty(arg,op.level) << ' ' << view;
						if( level > op.level ) os << ')';
					} else {// - s
						auto op = *ASSERTED(_prefixes.finds_value(view));
						if( level > op.level ) os << '(';
						os << view << ' ' << pretty(arg,op.rlevel);
						if( level > op.level ) os << ')';
					}
					return os;
				} else if( auto const& bin = sum->ref<Binary>() ) {// (+) s
					auto const& view = bin->view;
					auto op = *ASSERTED(_infixes.finds_value(view));
					if( auto const& cons = op.cons ) {
						if( auto const& pair = arg.binary(*cons) ) {// (+)(s,t) --> s + t
							if( level > op.llevel ) os << '(';
							os << pretty(pair->first,op.llevel) << ' ' << view << ' ' << pretty(pair->second,op.rlevel);
							if( level > op.llevel ) os << ')';
							return os;
						}
					} else {// (+) s --> (s +)
						return os << '(' << pretty(arg,op.llevel) << ' ' << view << ')';
					}
				} else if( auto op = sum->ref<Compr>() ) {// {x. s}
					if( auto const& abs = arg.bind() ) {
						return os << op->opener << pretty_sym(abs->first) << ". "
							<< pretty(abs->second,0) << op->closer;
					}
				} else if( auto const& op = sum->ref<BinderRel>() ) {// (∀∈)(A, x. P.[x]) → ∀x ∈ A. P.[x]
					if( op->cons )
					if( auto const& pair = arg.binary(*op->cons) )
					if( auto const& bind = pair->second.bind() ) {
						if( level > op->llevel ) os << '(';
						os << op->binder << pretty_sym(bind->first) << ' '
							<< op->mid << ' ' << pretty(pair->first,0) << ". "
							<< pretty(bind->second);
						if( level > op->llevel ) os << ')';
						return os;
					}
				} else if( auto const& op = sum->ref<ComprRel>() ) {// {_∈_._}(A, x. P.[x]) → {x ∈ A. P.[x]}
					if( op->cons )
					if( auto const& pair = arg.binary(*op->cons) )
					if( auto const& bind = pair->second.bind() ) {
						return os << op->opener << pretty_sym(bind->first) << ' '
							<< op->mid << ' ' << pretty(pair->first,0) << ". "
							<< pretty(bind->second) << op->closer;
					}
				} else if( auto const& op = sum->ref<Singleton>() ) {// {_}
					return os << op->opener << pretty(arg,0) << op->closer;
				}
			}
		} else if( auto app_in = fun.app() ) {
			auto const& fun_in = app_in->first, arg_in = app_in->second;
			if( auto sym = fun_in.sym() ) {// f s t
				if( auto const& op = _prefixes.finds_value(*sym) ) {
					if( level > op->level ) os << '(';
					os << *sym << ' ';
					os << pretty(arg,op->rlevel);
					if( level > op->level ) os << ')';
					return os;
				} else if( auto const& sum = _pretty_of.finds_value(*sym) ) {
					if( auto const& bin = sum->ref<Binary>() ) {
						auto const& op = _infixes.finds_value(bin->view);
						if( level > op->level ) os << '(';
						os << pretty(arg_in,op->llevel);
						os << ' ' << *sym << ' ';
						os << pretty(arg,op->rlevel);
						if( level > op->level ) os << ')';
						return os;
					} else if( auto const& op = sum->ref<BinderRel>() ) {
						if( !op->cons )
						if( auto abs = arg.bind() ) {
							if( level > op->llevel ) os << '(';
							os << op->binder << ' ' << abs->first << ' ' << op->mid << ' ' << pretty(arg_in,op->rlevel) << ". " << pretty(abs->second,op->rlevel);
							if( level > op->llevel ) os << ')';
							return os;
						}
					} else if( auto const& op = sum->ref<ComprRel>() ) {// {_ ∈ _. _}
						if( !op->cons )
						if( auto const& abs = arg.bind() ) {
							return os << op->opener << pretty_sym(abs->first) << ' ' << op->mid << ' '
								<< pretty(app_in->second) << ". " << pretty(abs->second) << op->closer;
						}
					}
				}
			}
		}
		if( level >= 1000 ) {
			os << '(';
		}
		os << pretty(fun, 999) << ' ';
		os << pretty(arg, 1000);
		if( level >= 1000 ) {
			os << ')';
		}
		return os;
	} else if( auto abs = term.bind() ) {
		if( level > 0 ) {
			os << '(';
		}
		os << pretty_sym(abs->first) << ". " << pretty(abs->second, 0);
		if( level > 0 ) {
			os << ')';
		}
		return os;
	} else if( auto fix = term.unbind() ) {
		return os << fix->first << ".[" << pretty(fix->second,-1000) << ']';
	} else {
		assert(false);
	}
}
function<ostream&(ostream&)> Syntax::pretty_thms(StrMap<Thm> const& thms) const & {
	return [this,&thms](ostream& os) -> ostream& {
		for( auto const& thm : thms ) {
			os << "  thm " << thm.first << ": " << pretty(thm.second) << endl;
		}
		return os;
	};
}

ostream& Syntax::pretty_ctxt( ostream& os, Ctxt const& ctxt, size_t rev,
	function<ostream&(ostream&)> const& endl ) const & {
	function<void(ostream&,Term const&)> term = [this](ostream& os, Term const& t) {
		os << pretty(t);
	};
	if( auto p = ctxt.find_parent() ) {
		pretty_ctxt(os,p->first,p->second,endl);
	}
	if( _print_ctxt ) {
		os << "-- ctxt @" << ctxt.id() << endl;
	}
	for( int i = 0; i < rev; ) {
		if( auto sym = ctxt.fixed(i) ) {
			os << "\tfixes";
			do {
				os << ' ';
				pretty(os,*sym);
				i++;
			} while( sym = ctxt.fixed(i) );
			os << '.' << endl;
		}
		if( auto assume = ctxt.assumed(i) ) {
			os << "\tassumes " << pretty(*assume) << '.'<< endl;
			i++;
			continue;
		}
		if( auto obtain = ctxt.obtained(i) ) {
			auto [sym,thm,spec] = *obtain;
			os << "\tobtains " << sym << "\n\t  where " << pretty(spec) << '.' << endl;
			i++;
			continue;
		}
		break;
	}
	return os;
}

function<ostream&(ostream&)> Syntax::pretty_subst(Subst const& subst) const & {
	return [&subst,this](ostream& os)->ostream&{
		static function<void(ostream&,pair<string const,Opt<Term>> const&)> const& pair = [this]( ostream& os, auto const& p ){
			auto const& [var,val] = p;
			os << pretty(var) << " := " << pretty( val ? *val : var );
		};
		os << '@' << subst.ctxt().id() << " [ ";
		out_sep(os, subst.map().begin(), subst.map().end(), ",\n  ", pair );
		return os << " ]";
	};
}
