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


class SubstDag : public CSubst, public Graph<std::string,std::less<>> {
public:
	struct Cyclic : std::exception {};
	/**
	 * @brief assigns a variable a value, while maintaining acyclicity
	 * 
	 * @param var 
	 * @param val 
	 */
	void assign(std::string const& var, CTerm const& val) {
		if( val != var ) {
			CSubst::assign(var,val);
			val.iter_syms([](auto){},
				[&](std::string_view const& sym) {
					if( has_path(sym,var) ) {
						throw Cyclic();
					}
					add_edge(var,sym);
				}
			);
		}
	}
	void close() {
		for( auto const& p : map() ) {
			CSubst::assign(p.first,get(p.first)->csubst(*this));
		}
	}
};

#endif
