#ifndef _MATCHER_HPP_
#define _MATCHER_HPP_
#include<list>
#include"core.hpp"

/**
 * @brief Automatically instantiate universally quantified variables so that implication premises are discharged.
 * 
 * @param t 
 * @param args 
 * @return the resulting theorem.
 */
Thm inst_discharge(Thm const& t, std::list<Thm> const& args);

#endif