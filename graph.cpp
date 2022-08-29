#include "graph.hpp"

template<typename _Key, typename _Compare>
bool Graph<_Key,_Compare>::has_path(_Key const& s, _Key const& t) const {
	if( s == t ) {
		return true;
	}
	for( size_t u : _edges[s] ) {
		if( has_path(u,t) ) {
			return true;
		}
	}
	return false;
}
