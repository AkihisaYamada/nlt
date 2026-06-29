#ifndef PAIR_HPP
#define PAIR_HPP
#include<utility>
/* 
 * Why not std::pair? Because it silently casts std::pair<T1&,T2&> into std::pair<T1,T2> without copying.
 * Here, if one obtains Pair<T1,T2>, then values are owned by the pair.
 */
template<typename T1, typename T2>
struct Pair {
	T1 first;
	T2 second;
	Pair() : first(),second() {}
	template<typename U1, typename U2>
	Pair( U1&& f, U2&& s ) : first(std::forward<U1>(f)), second(std::forward<U2>(s)) {}
	template<typename U1, typename U2>
	friend struct Pair;
	Pair( Pair<std::remove_cvref_t<T1>const&,std::remove_cvref_t<T2>const&> const& org ) : first(org.first), second(org.second) {}
	Pair( Pair<std::remove_cvref_t<T1>&&,std::remove_cvref_t<T2>const&> const& org ) : first(std::move(org.first)), second(org.second) {}
	Pair( Pair<std::remove_cvref_t<T1>const&,std::remove_cvref_t<T2>&&> const& org ) : first(org.first), second(std::move(org.second)) {}
};
template<typename T1, typename T2>
struct Pair<T1&,T2> {
    T1& first;
    T2 second;
	template<typename U2>
    Pair( T1& f, U2&& s ) : first(f), second(std::forward<U2>(s)) {}
    Pair( T1&&, auto ) = delete;
};
template<typename T1, typename T2>
struct Pair<T1,T2&> {
    T1 first;
    T2& second;
	template<typename U1>
    Pair( U1&& f, T2& s ) : first(std::forward<U1>(f)), second(s) {}
    Pair( auto, T2&& ) = delete;
};

template<typename T1, typename T2>
struct Pair<T1&,T2&> {
	T1& first;
	T2& second;
	Pair( T1& f, T2& s ) : first(f), second(s) {}
    Pair( T1&&, auto ) = delete;
    Pair( auto, T2&& ) = delete;
};

template<typename T1, typename T2, typename U1, typename U2>
bool operator==( Pair<T1,T2> const& x, Pair<U1,U2> const& y ) {
	return x.first == y.first && x.second == y.second;
}

#endif