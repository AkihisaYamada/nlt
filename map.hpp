#ifndef _MAP_HPP
#define _MAP_HPP

#include<map>
#include<type_traits>
#include"opt.hpp"
#include"pair.hpp"

template<typename K, typename T>
struct Map {
private:
	using _Body = std::map<K,T,std::less<>>;
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
	Pair<iterator,bool> emplace( Ka&& k, Va&& v ) {
		auto [it,fl] = _body.emplace(
			 std::piecewise_construct,
			 std::forward_as_tuple(std::forward<Ka>(k)),
			 std::forward_as_tuple(std::forward<Va>(v))
		);
		return {it,fl};
	}
	template<typename Ka>
	Pair<iterator,bool> emplace( Ka&& k, T&& v ) {
		auto [it,fl] = _body.emplace(std::forward<Ka>(k),std::move(v));
		return {it,fl};
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
	Opt<Pair<K const&,T&>> finds_pair( L&& k ) & {
		auto it = _body.find(std::forward<L>(k));
		if( it == _body.end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename L>
	Opt<Pair<K const&,T const&>> finds_pair( L&& k ) const & {
		auto it = _body.find(std::forward<L>(k));
		if( it == end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename Ka>
	Opt<T const&> finds_value( Ka&& k ) const& {
		return finds_pair(std::move(k)) >>= []( auto const& kv )->Opt<T const&>{ return kv.second; };
	}
	template<typename Ka>
	Opt<T&> finds_value( Ka&& k )& {
		return finds_pair(std::move(k)) >>= []( auto const& kv )->Opt<T&>{ return {kv.second}; };
	}
	template<typename Ka>
	Opt<Pair<K const&,T const&>> finds_bound( Ka&& k ) const & {
		auto it = _body.lower_bound(std::forward<Ka>(k));
		if( it == end() ) {
			return {};
		}
		return {{it->first,it->second}};
	}
	template<typename Ka>
		requires (!std::same_as<std::remove_cvref_t<Ka>, iterator> &&// avoid iterators to match
			!std::same_as<std::remove_cvref_t<Ka>, const_iterator>)
	bool erase( Ka&& k ) {
		auto it = _body.find(std::forward<Ka>(k));
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
	template<typename Ka>
	bool contains( Ka const& k ) const & {
		return _body.contains(k);
	}
};


template<typename K, typename T>
struct MMap {
private:
	using _Body = std::multimap<K,T,std::less<>>;
	_Body _body;
public:
	using iterator = _Body::iterator;
	using const_iterator = _Body::const_iterator;
	template<typename... Args>
		requires std::is_constructible_v<_Body,Args...>
	MMap( Args&&... args ) : _body( std::forward<Args>(args)... ) {}
	/* allows brace initialization */
	MMap( std::initializer_list<std::pair<K const, T>> il ) : _body(il) {}
	template<typename Ka>
	iterator emplace_front( Ka&& k, T&& v ) {
		auto it = _body.lower_bound(k);
		return _body.emplace_hint(it,std::forward<Ka>(k),std::move(v));
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
	template<typename Ka>
	Opt<Pair<K const&,T&>> finds_pair_front( Ka const& k ) & {
		if( auto it = _body.lower_bound(k); it != _body.end() && k == it->first ) {
			return {{it->first,it->second}};
		}
		return {};
	}
	template<typename Ka>
	Opt<Pair<K const&,T const&>> finds_pair_front( Ka const& k ) const & {
		if( auto it = _body.lower_bound(k); it != _body.end() && k == it->first ) {
			return {{it->first,it->second}};
		}
		return {};
	}
	template<typename Ka>
	Opt<T const&> finds_value_front( Ka&& k ) const& {
		return finds_pair_front(std::move(k)) >>= []( auto const& kv )->Opt<T const&>{ return kv.second; };
	}
	template<typename Ka>
	Opt<T&> finds_value_front( Ka&& k )& {
		return finds_pair_front(std::move(k)) >>= []( auto const& kv )->Opt<T&>{ return {kv.second}; };
	}
	template<typename Ka>
	Pair<iterator,iterator> equal_range( Ka&& k ) & {
		auto [it,end] = _body.equal_range( std::forward<Ka>(k) );
		return {it,end};
	}
	template<typename Ka>
	bool erase_front( Ka const& k ) {
		if( auto it = _body.lower_bound(k); it != _body.end() && k == it->first ) {
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
	template<typename Ka>
	bool contains( Ka const& k ) const & {
		return _body.contains(k);
	}
};

#endif
