#ifndef _DEBUG_HPP_
#define _DEBUG_HPP_

#include<ostream>
#include"core.hpp"
#include"syntax.hpp"

#define DEB(expr) do { std::cerr << __FILE__ << ":" << __LINE__ << ": " << expr << endl; } while(0)

#endif
