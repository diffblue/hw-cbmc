/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/namespace.h>
#include <util/threeval.h>
#include <util/arith_tools.h>

#include <langapi/language_util.h>

//#include "instantiate.h"
#include "counterexample_netlist.h"

/*******************************************************************\

Function: show_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_state(
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  unsigned timeframe)
{
  std::cout << "Transition system state " << timeframe << "\n";
  std::cout << "----------------------------------------------------\n";

  for(var_mapt::mapt::const_iterator
      it=map.var_map.map.begin();
      it!=map.var_map.map.end(); it++)
  {
    const var_mapt::vart &var=it->second;
    
    if(var.is_latch() || var.is_input() || var.is_wire())
    {
      std::cout << it->first << "=";

      std::string value;

      for(unsigned i=0; i<var.bits.size(); i++)
      {
        literalt l=map.get(timeframe, var.bits[i]);

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

      if(var.type.id()==ID_range ||
         var.type.id()==ID_unsignedbv ||
         var.type.id()==ID_signedbv)
      {
        exprt value_expr;

        if(var.type.id()==ID_range)
        {
          mp_integer i=binary2integer(value, false);
          mp_integer from=string2integer(var.type.get_string(ID_from));
          value_expr = constant_exprt(integer2string(i + from), var.type);
        }
        else
          value_expr = constant_exprt(value, var.type);

        std::cout << from_expr(ns, it->first, value_expr);
        std::cout << " (" << value << ")";
      }
      else
        std::cout << value;

      std::cout << '\n';
    }
  }

  std::cout << std::endl;
}

/*******************************************************************\

Function: show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_counterexample(message_handlert &message_handler, const propt &solver,
                         const bmc_mapt &map, const namespacet &ns) {
  for(unsigned t=0; t<map.get_no_timeframes(); t++)
    show_state(solver, map, ns, t);
}

/*******************************************************************\

Function: show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_counterexample(const std::list<exprt> &properties,
                         const std::list<bvt> &prop_bv,
                         message_handlert &message_handler, const propt &solver,
                         const bmc_mapt &map, const namespacet &ns) {
  unsigned p=0;
  messaget message(message_handler);

  for(std::list<bvt>::const_iterator p_it=prop_bv.begin();
      p_it!=prop_bv.end();
      p_it++, p++)
  {
    const bvt &bv=*p_it;
    assert(bv.size()==map.get_no_timeframes());
  
    for(unsigned t=0; t<map.get_no_timeframes(); t++)
    {
      tvt result=solver.l_get(bv[t]);

      if(result.is_unknown())
      {
        message.warning() << "got unknown-valued property literal" 
                          << messaget::eom;
      }
      else if(result.is_false())
      {
        std::cout << "property "
                  << (p+1) 
                  << " violated in time frame " << t
                  << ":" << '\n' << '\n';

        for(unsigned x=0; x<=t; x++)
          show_state(solver, map, ns, x);

        std::cout << std::endl;
        break; // next property
      }
    }
  }
}
