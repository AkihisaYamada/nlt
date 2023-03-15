#ifndef _GRAPH_HPP
#define _GRAPH_HPP

#include<vector>
#include<set>
#include<map>
#include"ref.hpp"

template<typename _Key, typename _Compare = std::less<_Key>>
class Graph {
	std::map<_Key const,std::set<_Key>> _edges;
public:
	bool has_edge(_Key const& s, _Key const& t) const {
		return _edges[s].contains(t);
	}
	Graph add_edge(_Key const& s, _Key const& t) {
		_edges[s].insert(t);
		return *this;
	}
	bool has_path(_Key const& s, _Key const& t) const;
};


#endif
