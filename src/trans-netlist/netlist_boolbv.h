/*******************************************************************\

Module: boolbvt for Netlists

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_NETLIST_BOOLBV_H
#define CPROVER_TRANS_NETLIST_NETLIST_BOOLBV_H

#include <solvers/flattening/boolbv.h>

#include "var_map.h"

/*******************************************************************\

   Class: netlist_boolbvt

 Purpose:

\*******************************************************************/

class netlist_boolbvt : public boolbvt
{
public:
  netlist_boolbvt(
    const namespacet &_ns,
    propt &solver,
    message_handlert &message_handler,
    const var_mapt &_var_map)
    : boolbvt(_ns, solver, message_handler), var_map(_var_map)
  {
  }

  typedef boolbvt SUB;

  // overloading
  literalt convert_bool(const exprt &) override;
  bvt convert_bitvector(const exprt &expr) override;

  using boolbvt::get_literal;
  literalt get_literal(const std::string &symbol, const unsigned bit);

protected:
  // disable smart variable allocation,
  // we already have literals for all variables
  bool boolbv_set_equality_to_true(const equal_exprt &expr) override
  {
    // see if it is an unbounded array
    if(is_unbounded_array(expr.lhs().type()))
      return true;

    const bvt &bv_lhs = convert_bv(expr.lhs());
    const bvt &bv_rhs = convert_bv(expr.rhs());
    bv_utils.set_equal(bv_lhs, bv_rhs);
    return false;
  }
  bool set_equality_to_true(const equal_exprt &expr) override
  {
    return true;
  }

  const var_mapt &var_map;
};

#endif // CPROVER_TRANS_NETLIST_NETLIST_BOOLBV_H
