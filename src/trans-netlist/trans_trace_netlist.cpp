/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ctime>
#include <cassert>
#include <string>
#include <iostream>

#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/xml.h>

#include <langapi/language_util.h>

#include "instantiate_netlist.h"
#include "trans_trace_netlist.h"

/*******************************************************************\

Function: bitstring_to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bitstring_to_expr(const std::string &src, const typet &type)
{
  exprt value_expr;
  value_expr.make_nil();

  if(type.id()==ID_range ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv)
  {
    if(type.id()==ID_range)
    {
      mp_integer i=binary2integer(src, false);
      mp_integer from=string2integer(type.get_string(ID_from));
      value_expr = constant_exprt{integer2string(i + from), type};
    }
    else
      value_expr = constant_exprt{src, type};
  }
  else if(type.id()==ID_bool)
  {
    if(src=="0")
      value_expr=false_exprt();
    else if(src=="1")
      value_expr=true_exprt();
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    value_expr=exprt(ID_array, array_type);
    mp_integer size;
    to_integer_non_constant(array_type.size(), size);
    std::size_t size_int = size.to_ulong();
    value_expr.operands().resize(size_int);
    std::size_t op_width=src.size()/size_int;

    for(std::size_t i=0; i<size_int; i++)
      value_expr.operands()[size_int - i - 1] = bitstring_to_expr(
        std::string(src, i * op_width, op_width), array_type.element_type());
  }
  
  return value_expr;
}

/*******************************************************************\

Function: compute_trans_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compute_trans_trace(
  const bvt &prop_bv,
  const bmc_mapt &bmc_map,
  const propt &solver,
  const namespacet &ns,
  trans_tracet &dest)
{
  dest.states.reserve(bmc_map.get_no_timeframes());
  
  for(unsigned t=0; t<bmc_map.get_no_timeframes(); t++)
  {
    dest.states.push_back(trans_tracet::statet());
    trans_tracet::statet &state=dest.states.back();
  
    for(var_mapt::mapt::const_iterator
        it=bmc_map.var_map.map.begin();
        it!=bmc_map.var_map.map.end();
        it++)
    {
      const var_mapt::vart &var=it->second;

      // we show latches, inputs, wires      
      if(!var.is_latch() && !var.is_input() && !var.is_wire())
        continue;
        
      const symbolt &symbol=ns.lookup(it->first);

      std::string value;
      value.reserve(var.bits.size());

      for(unsigned i=0; i<var.bits.size(); i++)
      {
        literalt l=bmc_map.get(t, var.bits[i]);

        char ch;

        switch(solver.l_get(l).get_value())
        {
         case tvt::tv_enumt::TV_TRUE: ch='1'; break;
         case tvt::tv_enumt::TV_FALSE: ch='0'; break;
         case tvt::tv_enumt::TV_UNKNOWN:
         default: ch='?'; break;
        }

        value=ch+value;
      }
      
      state.assignments.push_back(trans_tracet::statet::assignmentt());

      trans_tracet::statet::assignmentt &assignment=
        state.assignments.back();

      assignment.lhs=symbol.symbol_expr();
      assignment.rhs=bitstring_to_expr(value, var.type);
      assignment.location.make_nil();
    }

    // check the property
    assert(t<prop_bv.size());
    tvt result=solver.l_get(prop_bv[t]);
    state.property_failed=result.is_false();
  }
}         
          
