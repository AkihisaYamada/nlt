#include "parser.hpp"

using namespace std;

Opt<string> Parser::gets_thm_name() & {
	return gets(Lexer::Word|Lexer::Number);
}
string Parser::get_thm_name() & {
	if( auto const& opt = gets_thm_name() ) {
		return *opt;
	}
	throw Error("Required a theorem name");
}

Term Parser::_nest_abs( Term const& bind, int level, string& fv ) & {
	if( auto next = gets(Lexer::Word) ) {
		return bind( *next /= _nest_abs(bind,level,fv) );
	}
	skip(".");
	return _get_term(level,fv);
}

Opt<Term> Parser::_gets_term( int level, string& fv ) & {
	auto& syn = syntax();
	string_view peek = peek_token();
	if( peek == "" || syn.has_closer(peek) ) {
		return {};
	}
	Term init;
	if( skips("(") ) {
		init = _get_term(-1000,fv);
		skip(")");
	} else if( auto const& x = syn.finds_opener(peek) ) {
		ignore_token();
		auto const& [opener,op] = *x;
		if( auto const& var = gets_sym() ) {
			auto const& follow = peek_token();
			if( follow == "." ) {
				ignore_token();
				auto body = _get_term(0,fv);
				skip(op.closer);
				if( !op.compr ) throw Error("\"comprehension not registered\"")(string("\"")+opener+"\"");
				init = Term(*op.compr)(*var/=body);
			} else if( auto y = op.bcompr.finds(follow) ) {
				ignore_token();
				auto bcompr = y->second;
				auto range = _get_term(0,fv);
				skip(".");
				auto body = _get_term(0,fv);
				skip(op.closer);
				init = Term(bcompr)(range)(*var/=body),level;
			} else {
				auto inner = _get_follow(*var,0,syn,fv);
				skip(op.closer);
				if( !op.singleton ) throw Error("\"singleton not registered\"")(inner);
				init = Term(*op.singleton)(inner);
			}
		} else {
			skip(op.closer);
			if( !op.empty ) throw Error("\"empty not registered\"");
			init = *op.empty;
		}
	} else if( auto x = syn.finds_prefix(peek) ) {
		auto const& [binder,op] = *x;
		if( op.llevel < level ) {
			return {};
		}
		ignore_token();
		if( auto const& r = _gets_term(x->second.rlevel,fv) ) {
			init = Term(binder)(*r);
		} else {
			init = binder;
		}
	} else if( auto x = syn.finds_binder(peek) ) {
		auto const& [binder,op] = *x;
		if( op.llevel < level ) {
			return {};
		}
		ignore_token();
		if( auto var = gets_sym() ) {
			auto follow = get();
			if( follow == "." ) {// ∀x. _
				auto body = _get_term(op.rlevel,fv);
				init = Term(binder)(*var/=body);
			} else if( auto y = op.bbinds.finds(follow) ) {// ∀x ∈ X. _
				auto actual = y->second;
				auto range = _get_term(0,fv);
				skip(".");
				auto body = _get_term(op.rlevel,fv);
				init = Term(actual)(range)(*var/=body);
			} else {
				auto inner = _nest_abs(binder,op.rlevel,fv);
				init = Term(binder)( *var /= Term(binder)(follow/=inner) );
			}
		} else {
			init = binder;
		}
	} else if( auto x = syn.finds_infix(peek) ) {
		if( x->second.level < level ) {
			return {};
		}
		init = Term(x->first);
		ignore_token();
	} else {
		auto sym = string(peek);
		ignore_token();
		if( level < 0 && skips(".") ) {
			auto body = _gets_term(level,fv);
			if( !body ) throw Error("\"binding expects body\"");
			init = sym /= *body;
		} else if( skips(".[") ) {
			auto const& body = _gets_term(-1000,fv);
			if( !body ) throw Error("\"unbinding expects body\"");
			skip("]");
			init = sym %= *body;
		} else {
			init = sym;
		}
	}
	return {_get_follow(init,level,syn,fv)};
}

/**
 * @param pat should be variables combined by `,`
 * @param dir will map each variable to its address. 
 */
static void _parse_pattern( StrMap<vector<Term>>& dir, vector<Term>& addr, Term const& pat ) {
	if( auto sym = pat.sym() ) {
		if( dir.contains(*sym) ) throw Error("\"nonlinear binding\"")(pat);
		dir.emplace(*sym,addr);
	} else if( auto pair = pat.binary(",") ) {// TODO: generalize
		addr.push_back("fst");
		_parse_pattern(dir,addr,pair->first);
		addr.back() = "snd";
		_parse_pattern(dir,addr,pair->second);
		addr.pop_back();
	} else {
		throw Error("\"invalid pattern\"")(pat);
	}
}
static auto _tuple_binder( Term const& pat, string& fv ) {
	auto dir = StrMap<vector<Term>>{};// if pat = (x,y,z), then x -> {fst}, y -> {snd,fst}, z -> {snd,snd}
	auto addr = vector<Term>();
	_parse_pattern(dir,addr,pat);
	auto map = StrMap<Term>{};// x -> fst tp, y -> fst (snd tp), z -> snd (snd tp)
	string tp = fv;
	rename_var(fv);
	for( auto const& [var,addr] : dir ) {
		auto val = Term(tp);
		for( auto const& prj : addr ) {
			val = prj(val);
		}
		map.emplace(var,val);
	}
	return [tp,map]( Term const& body ){
		auto mapper = [&]( string_view const& v )->Opt<Term>{
			if( auto a = map.finds(v) ) {
				return {a->second};
			}
			return {};
		};
		return tp /= body.map(mapper);// tp. body[x := fst tp, y := fst (snd tp), z := snd (snd tp)]
	};
}

Term Parser::_get_follow( Term ret, int level, Syntax const& syn, string& fv ) & {
	int lastlevel = INT_MAX;
	for(;;) {
		string_view peek = peek_token();
		if( peek == "" || syn.has_closer(peek) ) {
			return ret;
		}
		if( peek == "." ) {
			if( 0 <= level ) return ret;
			ignore_token();// structured binding
			return _tuple_binder(ret,fv)(_get_term(0,fv));
		}
		if( auto x = syn.finds_infix(peek) ) {
			auto [sym,op] = *x;
			if( op.level < level ) return ret;
			if( lastlevel < op.llevel ) return ret;
			ignore_token();
			auto const& r = _gets_term(op.rlevel,fv);
			if( !r ) return Term(sym)(ret);
			lastlevel = op.level;
			ret = Term(sym)(ret)(*r);
		} else {
			if( 1000 <= level ) return ret;
			auto const& r = _gets_term(1000,fv);
			if( !r ) return ret;
			ret = ret(*r);
		}
	}
}

Opt<string> Parser::gets_sym() & {
	auto& syn = syntax();
	string_view peek = peek_token();
	if( peek == "(" ) {
		ignore_token();
		auto ret = get();
		skip(")");
		return {ret};
	}
	if( peek == "" || syn.has_closer(peek) || syn.finds_opener(peek) || syn.finds_binder(peek) || syn.finds_prefix(peek) || syn.finds_infix(peek) ) {
		return {};
	}
	return {get()};
}
string Parser::get_sym() & {
	if( auto o = gets_sym() ) {
		return *o;
	}
	throw Error("\"expected a symbol\"")(get());
}