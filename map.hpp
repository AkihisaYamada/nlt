#ifndef _MAP_HPP
#define _MAP_HPP

#include<map>
#include"opt.hpp"

template<typename K, typename T>
class Map : std::map<K,T,std::less<>> {
	using M = std::map<K,T,std::less<>>;
public:
	using typename M::value_type, M::iterator, M::const_iterator;
	using M::map, M::find, M::insert, M::begin, M::end, M::size, M::empty;
	/**
	 * @brief emplaces a key-value pair.
	 * @return the pair of the iterator to the key-value pair and bool if insertion took place
	 */
	template<typename... Ts>
	std::pair<iterator, bool> emplace( Ts&&... args ) {
		return M::emplace(std::forward<Ts>(args)...);
	}
	template<typename L>
	Opt<std::pair<K const,T>&> finds( L const& k ) & {
		auto it = M::find(k);
		if( it == end() ) {
			return {};
		}
		return *it;
	}
	Opt<std::pair<K const,T>&> finds( K const& k ) & {
		return finds<K>(k);
	}
	template<typename L>
	Opt<std::pair<K const,T> const&> finds( L const& k ) const & {
		auto it = M::find(k);
		if( it == end() ) {
			return {};
		}
		return *it;
	}
	Opt<std::pair<K const,T> const&> finds( K const& k ) const & {
		return finds<K>(k);
	}
	template<typename L>
	void erase( L const& k ) {
		auto it = M::find(k);
		if( it != end() ) {
			M::erase(it);
		}
	}
	iterator erase( iterator const& it ) {
		return M::erase(it);
	}
	template<typename L>
	bool contains( L const& k ) const & {
		return M::contains(k);
	}
};

#endif
