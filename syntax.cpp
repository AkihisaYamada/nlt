#include "syntax.hpp"

using namespace std;

Syntax SYNTAX;

Syntax::Syntax() {
	infix("⟹",0,1,0,{});
	binder("∀",0,0);
	infix(".",-1,-1,-2,{});
	_closers.emplace(")");
	_closers.emplace("]");
}

ostream& Syntax::pretty_sym( ostream& os, string_view const& sym ) const & {
	if( _prefixes.contains(sym) || _binders.contains(sym) || _infixes.contains(sym) || _pretty_of.contains(sym) ) {
		return os << '(' << sym << ')';
	}
	if( auto const& x = _pretty_of.finds(sym) ) {
		if( auto y = x->second.ref<Empty>() ) {
			return os << y->opener << y->closer;
		}
	}
	return os << sym;
}

ostream& Syntax::pretty( ostream& os, Term const& term, int level ) const & {
	if( auto const& sym = term.sym() ) {
		return pretty_sym(os,*sym);
	} else if( auto const& app = term.app() ) {
		auto const& fun = app->first, arg = app->second;
		if( auto const& sym = fun.sym() ) {// unary
			if( auto const& x = _prefixes.finds(*sym) ) {
				auto const& op = x->second;
				if( level > op.llevel ) os << '(';
				os << *sym << ' ' << pretty(arg,op.rlevel);
				if( level > op.llevel ) os << ')';
				return os;
			} else if( auto const& x = _binders.finds(*sym) ) {// ∀x. _
				auto const& op = x->second;
				if( auto const& abs = arg.bind() ) {
					if( level > op.llevel ) os << '(';
					os << *sym << ' ' << pretty_sym(abs->first);
					Term cur = abs->second;
					while( auto abs2 = cur.binder(*sym) ) {
						os << ' ' << pretty_sym(abs2->first);
						cur = abs2->second;
					}
					os << ". " << pretty(cur,op.rlevel);
					if( level > op.llevel ) os << ')';
					return os;
				}
			} else if( auto const& x = _pretty_of.finds(*sym) ) {
				auto const& sum = x->second;
				if( auto const& abs = arg.bind() ) {
					if( auto op = sum.ref<Compr>() ) {// {x. _}
						return os << op->opener << pretty_sym(abs->first) << ". "
							<< pretty(abs->second,0) << op->closer;
					}
				} else if( auto const& op = sum.ref<BinderRel>() ) {// (∀∈)(A, x. P.[x]) → ∀x ∈ A. P.[x]
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
				} else if( auto const& op = sum.ref<ComprRel>() ) {// {_∈_._}(A, x. P.[x]) → {x ∈ A. P.[x]}
					if( op->cons )
					if( auto const& pair = arg.binary(*op->cons) )
					if( auto const& bind = pair->second.bind() ) {
						return os << op->opener << pretty_sym(bind->first) << ' '
							<< op->mid << ' ' << pretty(pair->first,0) << ". "
							<< pretty(bind->second);
					}
				} else if( auto const& op = sum.ref<Singleton>() ) {// {_}
					return os << op->opener << pretty(arg,0) << op->closer;
				}
			} else if( auto const& x = finds_infix(*sym) ) {
				auto const& op = x->second;
				if( auto const& cons = op.cons )
				if( auto const& pair = arg.binary(*cons) ) {
					if( level > op.llevel ) os << '(';
					os << pretty(pair->first,op.llevel) << ' ' << *sym << ' ' << pretty(pair->second,op.rlevel);
					if( level > op.llevel ) os << ')';
					return os;
				}
			}
		} else if( auto app_in = fun.app() ) {
			auto const& fun_in = app_in->first, arg_in = app_in->second;
			if( auto sym = fun_in.sym() ) {// binary
				if( auto const& x = _prefixes.finds(*sym) ) {
					auto const& op = x->second;
					if( level > op.llevel ) os << '(';
					os << *sym << ' ';
					os << pretty(arg,op.rlevel);
					if( level > op.llevel ) os << ')';
					return os;
				} else if( auto const& x = _infixes.finds(*sym) ) {
					auto const& op = x->second;
					if( level > op.level ) os << '(';
					os << pretty(arg_in,op.llevel);
					os << ' ' << *sym << ' ';
					os << pretty(arg,op.rlevel);
					if( level > op.level ) os << ')';
					return os;
				} else if( auto const& x = _pretty_of.finds(*sym) ) {
					auto const& sum = x->second;
					if( auto const& op = sum.ref<BinderRel>() ) {
						if( !op->cons )
						if( auto abs = arg.bind() ) {
							if( level > op->llevel ) os << '(';
							os << op->binder << ' ' << abs->first << ' ' << op->mid << ' ' << pretty(arg_in,op->rlevel) << ". " << pretty(abs->second,op->rlevel);
							if( level > op->llevel ) os << ')';
							return os;
						}
					} else if( auto const& op = sum.ref<ComprRel>() ) {// {_ ∈ _. _}
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

ostream& Syntax::pretty_ctxt( ostream& os, Ctxt const& ctxt, size_t rev ) const & {
	function<void(ostream&,Term const&)> term = [this](ostream& os, Term const& t) {
		os << pretty(t);
	};
	if( auto p = ctxt.find_parent() ) {
		pretty_ctxt( os, p->first, p-> second );
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
