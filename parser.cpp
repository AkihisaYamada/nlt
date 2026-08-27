#include<limits>
#include "parser.hpp"
#include "lexer.hpp"

using namespace std;

Opt<string> Parser::gets_thm_name() & {
	return gets(Lexer::WORD|Lexer::NUMBER);
}
string Parser::get_thm_name() & {
	if( auto const& opt = gets_thm_name() ) {
		return *opt;
	}
	throw Error("Required a theorem name");
}
string Parser::get_thy_name() & {
	if( auto const& opt = gets(Tokenizer::WORD) ) {
		return *opt;
	}
	throw Error("Required a theory name");
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
static function<Term(Term const&)> _bind( Term const& pat, string& fv ) {
	if( auto sym = pat.sym() ) {// regular variable binding
		return [v=*sym]( Term const& body ){ return v/= body; };
	}
	// pattern binding, e.g. pat = (x,y,z)
	auto dir = StrMap<vector<Term>>{};// x -> {fst}, y -> {snd,fst}, z -> {snd,snd}
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
			return map.finds_value(v);
		};
		return tp /= body.map(mapper);// tp. body[x := fst tp, y := fst (snd tp), z := snd (snd tp)]
	};
}

Term Parser::_nest_abs( string const& binder, Syntax::Binder const& op, string& fv ) & {
	if( auto next = _gets_term(INT_MAX,fv) ) {
		auto f = _bind(*next,fv);
		return Term(binder)(f(_nest_abs(binder,op,fv)));
	}
	skip(".");
	return _get_term(op.rlevel,fv);
}

Opt<Term> Parser::_gets_term( int level, string& fv ) & {
	auto& syn = syntax();
	string_view peek = peek_token();
	if( peek == "" ) return {};
	if( auto const& op = syn.finds_postfix(peek) ) {
		if( op->level < level ) return {};
		ignore_token();
		return {op->actual};
	}
	Term init;
	if( skips("(") ) {
		init = _get_term(Syntax::PARSE_ALL,fv);
		skip(")");
	} else if( next_token_type() == NUMBER ) {
		unsigned int num = get_nat();
		switch( num ) {
			case 0: init = "0"; break;
			case 1: init = "1"; break;
			case 2: init = "2"; break;
			case 3: init = "3"; break;
			default: {
				unsigned int bit = std::bit_floor(num);
				init = "1";// top bit
				for(;;) {
					bit >>= 1;
					if( bit == 0 ) break;
					init = Term( num & bit ? Syntax::BIT1 : Syntax::BIT0 )(init); 
				}
			}
		}
	} else if( auto const& x = syn.finds_opener(peek) ) {
		auto const& [opener,op] = *x;
		if( op.level < level ) {
			return {};
		}
		ignore_token();
		if( auto fst = gets_term(INT_MAX) ) {
			auto const& follow = peek_token();
			if( follow == "." ) {// {_. _}
				ignore_token();
				auto body = _get_term(0,fv);
				skip(op.closer);
				if( !op.compr ) throw Error("\"comprehension not registered\"")(string("\"")+opener+"\"");
				init = Term(*op.compr)(_bind(*fst,fv)(body));
			} else if( auto y = op.bcompr.finds_pair(follow) ) {// {_ < _. _}
				ignore_token();
				auto [actual,cons] = y->second;
				auto range = _get_term(0,fv);
				skip(".");
				auto body = _get_term(0,fv);
				skip(op.closer);
				auto bind = _bind(*fst,fv)(body);
				init = Term(actual);
				init = cons ? init(Term(*cons)(range)(bind)) : init(range)(bind);
			} else {// { _ }
				auto inner = _get_follow(*fst,0,syn,fv);
				skip(op.closer);
				if( !op.singleton ) throw Error("\"singleton not registered\"")(inner);
				init = Term(*op.singleton)(inner);
			}
		} else {// {}
			skip(op.closer);
			if( !op.empty ) throw Error("\"empty not registered\"");
			init = *op.empty;
		}
	} else if( auto op = syn.finds_prefix(peek) ) {
		if( op->level < level ) {
			return {};
		}
		ignore_token();
		if( auto const& r = _gets_term(op->rlevel,fv) ) {
			init = Term(op->actual)(*r);
		} else {
			init = op->actual;
		}
	} else if( auto x = syn.finds_binder(peek) ) {// ∀ ...
		auto const& [binder,op] = *x;
		if( op.llevel < level ) {
			return {};
		}
		ignore_token();
		vector<Pair<function<Term(Term const&)>,vector<function<Term(Term const&)>>>> range_params;
		while( auto const& fst = gets_term(INT_MAX) ) {// ∀x y z ...
			vector<function<Term(Term const&)>> params = {_bind(*fst,fv)};
			while( auto const& param = gets_term(INT_MAX) ) {
				params.emplace_back(_bind(*param,fv));
			}
			auto const& follow = peek_token();
			if( auto y = op.bbinds.finds_value(follow) ) {// ∀x y z ∈ X ...
				ignore_token();
				auto const& [actual,cons] = *y;
				auto const& range = _get_term(0,fv);
				auto f = [&]()->function<Term(Term const&)>{
					if( cons ) {
						return [actual,range,cons=*cons]( Term const& bind ){
							return Term(actual)(Term(cons)(range)(bind));
						};
					}
					return [actual,range]( Term const& bind ){
						return Term(actual)(range)(bind);
					};
				}();
				range_params.emplace_back(std::move(f),std::move(params));
				if( skips(",") ) continue;// ∀x y z ∈ X, ...
			} else {
				range_params.emplace_back(
					[&binder]( Term const& bind ){ return Term(binder)(bind); }, std::move(params)
				);
			}
			break;
		}
		size_t n = range_params.size();
		if( n == 0 ) {
			init = binder;
		} else {
			skip(".");
			init = _get_term(op.rlevel,fv);
			do {
				n--;
				auto const& [f,binds] = range_params[n];
				for( size_t m = binds.size(); m != 0; ) {
					m--;
					init = f(binds[m](init));
				}
			} while( n != 0 );
		}
	} else if( auto x = syn.finds_infix(peek) ) {// + ...
		if( level != Syntax::PARSE_ALL ) {
			return {};
		}
		init = Term(x->actual);
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

Term Parser::_get_follow( Term ret, int level, Syntax const& syn, string& fv ) & {
	int lastlevel = INT_MAX;
	for(;;) {
		string_view peek = peek_token();
		if( peek == "" ) {
			return ret;
		}
		if( peek == "." ) {
			if( 0 <= level ) return ret;
			ignore_token();// structured binding
			return _bind(ret,fv)(_get_term(0,fv));
		}
		if( auto op = syn.finds_postfix(peek) ) {// ret!
			if( op->level < level ) return ret;
			if( lastlevel < op->level ) return ret;
			ignore_token();
			ret = Term(op->actual)(ret);
		} else if( auto op = syn.finds_infix(peek) ) {// ret + ...
			if( op->level < level ) return ret;
			if( lastlevel < op->llevel ) return ret;
			ignore_token();
			if( auto const& tp = op->cons ) {
				auto const& r = _get_term(op->rlevel,fv);
				ret = Term(op->actual)(Term(*tp)(ret)(r));
			} else {
				auto const& r = _gets_term(op->rlevel,fv);
				if( !r ) return Term(op->actual)(ret);
				ret = Term(op->actual)(ret)(*r);
			}
			lastlevel = op->level;
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
	if( peek == "" || syn.finds_opener(peek) || syn.finds_binder(peek) || syn.finds_prefix(peek) || syn.finds_infix(peek) || syn.finds_postfix(peek) ) {
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