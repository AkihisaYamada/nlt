#ifndef _MAP_HPP
#define _MAP_HPP

#include<map>
#include<type_traits>
#include"opt.hpp"
#include"pair.hpp"

template<typename K, typename T, bool multi = false>
struct Map {
private:
	using _Body = typename std::conditional_t<multi,std::multimap<K,T,std::less<>>,std::map<K,T,std::less<>>>;
	_Body _body;
public:
	using iterator = _Body::iterator;
	using const_iterator = _Body::const_iterator;
	template<typename... Args>
		requires std::is_constructible_v<_Body,Args...>
	Map( Args&&... args ) : _body( std::forward<Args>(args)... ) {}
	/* allows brace initialization */
	Map( std::initializer_list<std::pair<K const, T>> il ) : _body(il) {}
	/**
	 * @brief emplaces a key-value pair.
	 * @return the pair of the iterator to the key-value pair and bool if insertion took place
	 */
	template<typename Ka, typename Va>
	Pair<iterator,bool> emplace( Ka&& k, Va&& v ) requires (!multi) {
		auto [it,fl] = _body.emplace(
			 std::piecewise_construct,
			 std::forward_as_tuple(std::forward<Ka>(k)),
			 std::forward_as_tuple(std::forward<Va>(v))
		);
		return {it,fl};
	}
	template<typename Ka>
	Pair<iterator,bool> emplace( Ka&& k, T&& v ) requires (!multi) {
		auto [it,fl] = _body.emplace(std::forward<Ka>(k),std::move(v));
		return {it,fl};
	}
	template<typename Ka>
	iterator emplace( Ka&& k, T&& v ) requires multi {
		return _body.emplace(std::forward<Ka>(k),std::move(v));
	}
	iterator begin() & {
		return _body.begin();
	}
	const_iterator begin() const & {
		return _body.begin();
	}
	const_iterator end() const& {
		return _body.end();
	}
	template<typename L>
	Opt<Pair<K const&,T&>> finds( L&& k ) & {
		auto it = _body.find(std::forward<L>(k));
		if( it == _body.end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename L>
	Opt<Pair<K const&,T const&>> finds( L&& k ) const & {
		auto it = _body.find(std::forward<L>(k));
		if( it == end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename L>
	Opt<Pair<K const&,T const&>> finds_bound( L&& k ) const & {
		auto it = _body.lower_bound(std::forward<L>(k));
		if( it == end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename L>
	Pair<iterator,const_iterator> equal_range( L&& k ) & requires multi {
		auto [it,end] = _body.equal_range( std::forward<L>(k) );
		return {it,end};
	}
	template<typename L>
		requires (!std::same_as<std::remove_cvref_t<L>, iterator> &&// avoid iterators to match
			!std::same_as<std::remove_cvref_t<L>, const_iterator>)
	bool erase( L&& k ) {
		auto it = _body.find(std::forward<L>(k));
		if( it != end() ) {
			_body.erase(it);
			return true;
		}
		return false;
	}
	iterator erase( iterator const& it ) {
		return _body.erase(it);
	}
	iterator erase( iterator const& it, const_iterator const& end ) {
		return _body.erase(it,end);
	}
	template<typename L>
	bool contains( L const& k ) const & {
		return _body.contains(k);
	}
};
template<typename K, typename T>
using MMap = Map<K,T,true>;

#endif
