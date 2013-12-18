/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>

#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/i2string.h>

#include "instantiate.h"

/*******************************************************************\

   Class: instantiate_bmc_mapt

 Purpose:

\*******************************************************************/

class instantiate_bmc_mapt:public boolbvt
{
public:
  instantiate_bmc_mapt(
    const namespacet &_ns,
    propt &solver,
    const bmc_mapt &_bmc_map,
    unsigned _current,
    unsigned _next):
    boolbvt(_ns, solver),
    bmc_map(_bmc_map),
    current(_current),
    next(_next)
  {
  }
  
  typedef boolbvt SUB;

  // overloading
  using boolbvt::get_literal;
  
  virtual literalt convert_bool(const exprt &expr);
  virtual literalt get_literal(const std::string &symbol, const unsigned bit);
  virtual void convert_bitvector(const exprt &expr, bvt &bv);
   
protected:   
  // disable smart variable allocation,
  // we already have literals for all variables
  virtual bool boolbv_set_equality_to_true(const equal_exprt &expr) { return true; }
  virtual bool set_equality_to_true(const equal_exprt &expr) { return true; }
  
  const bmc_mapt &bmc_map;
  unsigned current, next;
};

/*******************************************************************\

Function: instantiate_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_constraint(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message)
{
  instantiate_bmc_mapt i(ns, solver, bmc_map, current, next);

  i.set_message_handler(message.get_message_handler());

  try
  {
    i.set_to_true(expr);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message)
{
  instantiate_bmc_mapt i(ns, solver, bmc_map, current, next);

  i.set_message_handler(message.get_message_handler());

  try
  {
    return i.convert(expr);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message,
  bvt &bv)
{
  instantiate_bmc_mapt i(ns, solver, bmc_map, current, next);

  i.set_message_handler(message.get_message_handler());

  try
  {
    i.convert_bitvector(expr, bv);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_bmc_mapt::convert_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_bmc_mapt::convert_bool(const exprt &expr)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    bvt result;
    convert_bitvector(expr, result);

    if(result.size()!=1)
      throw "expected one-bit result";

    return result[0];
  }

  return SUB::convert_bool(expr);
}

/*******************************************************************\

Function: instantiate_bmc_mapt::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_bmc_mapt::convert_bitvector(const exprt &expr, bvt &bv)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    unsigned width=boolbv_width(expr.type());

    if(width!=0)
    {
      unsigned timeframe=(expr.id()==ID_symbol)?current:next;

      bv.resize(width);

      for(unsigned i=0; i<width; i++)
        bv[i]=bmc_map.get(timeframe, identifier, i);

      return;
    }
  }

  return SUB::convert_bitvector(expr, bv);
}

/*******************************************************************\

Function: instantiate_bmc_mapt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_bmc_mapt::get_literal(
  const std::string &symbol,
  const unsigned bit)
{
  return bmc_map.get(current, symbol, bit);
}

/*******************************************************************\

   Class: instantiate_var_mapt

 Purpose:

\*******************************************************************/

class instantiate_var_mapt:public boolbvt
{
public:
  instantiate_var_mapt(
    const namespacet &_ns,
    propt &solver,
    const var_mapt &_var_map):
    boolbvt(_ns, solver),
    var_map(_var_map)
  {
  }
  
  typedef boolbvt SUB;

  // overloading
  using boolbvt::get_literal;
  
  virtual literalt convert_bool(const exprt &expr);
  virtual literalt get_literal(const std::string &symbol, const unsigned bit);
  virtual void convert_bitvector(const exprt &expr, bvt &bv);
   
protected:   
  // disable smart variable allocation,
  // we already have literals for all variables
  virtual bool boolbv_set_equality_to_true(const equal_exprt &expr) { return true; }
  virtual bool set_equality_to_true(const equal_exprt &expr) { return true; }
  
  const var_mapt &var_map;
};

/*******************************************************************\

Function: instantiate_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_constraint(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message)
{
  instantiate_var_mapt i(ns, solver, var_map);

  i.set_message_handler(message.get_message_handler());

  try
  {
    i.set_to_true(expr);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message)
{
  instantiate_var_mapt i(ns, solver, var_map);

  i.set_message_handler(message.get_message_handler());

  try
  {
    return i.convert(expr);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message,
  bvt &bv)
{
  instantiate_var_mapt i(ns, solver, var_map);

  i.set_message_handler(message.get_message_handler());

  try
  {
    i.convert_bitvector(expr, bv);
  }

  catch(const char *err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }

  catch(const std::string &err)
  {
    std::cerr << err << std::endl;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_var_mapt::convert_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_var_mapt::convert_bool(const exprt &expr)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    bvt result;
    convert_bitvector(expr, result);

    if(result.size()!=1)
      throw "expected one-bit result";

    return result[0];
  }

  return SUB::convert_bool(expr);
}

/*******************************************************************\

Function: instantiate_var_mapt::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_var_mapt::convert_bitvector(const exprt &expr, bvt &bv)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    bool next=(expr.id()==ID_next_symbol);
    const irep_idt &identifier=expr.get(ID_identifier);

    unsigned width=boolbv_width(expr.type());

    if(width!=0)
    {
      bv.resize(width);

      for(unsigned i=0; i<width; i++)
        bv[i]=next?var_map.get_next(identifier, i)
                  :var_map.get_current(identifier, i);

      return;
    }
  }

  return SUB::convert_bitvector(expr, bv);
}

/*******************************************************************\

Function: instantiate_var_mapt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_var_mapt::get_literal(
  const std::string &symbol,
  const unsigned bit)
{
  return var_map.get_current(symbol, bit);
}

/*******************************************************************\

Function: timeframe_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string timeframe_identifier(
  unsigned timeframe,
  const irep_idt &identifier)
{
  return id2string(identifier)+"@"+i2string(timeframe);
}

/*******************************************************************\

   Class: wl_instantiatet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class wl_instantiatet
{
public:
  wl_instantiatet(
    unsigned _current,
    const namespacet &_ns):
    current(_current),
    ns(_ns)
  {
  }
  
  void instantiate(exprt &expr)
  {
    instantiate_rec(expr);
  }

protected:
  unsigned current;
  const namespacet &ns;
  
  void instantiate_rec(exprt &expr);
  void instantiate_rec(typet &expr);

};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void wl_instantiatet::instantiate_rec(exprt &expr)
{
  instantiate_rec(expr.type());

  if(expr.id()==ID_next_symbol || expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    if(expr.id()==ID_next_symbol)
    {
      expr.id(ID_symbol);
      expr.set(ID_identifier, timeframe_identifier(current+1, identifier));
    }
    else
    {
      expr.set(ID_identifier, timeframe_identifier(current, identifier));
    }
  }
  else
  {
    Forall_operands(it, expr)
      instantiate_rec(*it);
  }
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void wl_instantiatet::instantiate_rec(typet &type)
{
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate(
  exprt &expr,
  unsigned current,
  const namespacet &ns)
{
  wl_instantiatet wl_instantiate(current, ns);
  wl_instantiate.instantiate(expr);
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate(
  decision_proceduret &decision_procedure,
  const exprt &expr,
  unsigned current,
  const namespacet &ns)
{
  exprt tmp(expr);
  instantiate(tmp, current, ns);
  decision_procedure.set_to_true(tmp);
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_convert(
  prop_convt &prop_conv,
  const exprt &expr,
  unsigned current,
  const namespacet &ns)
{
  exprt tmp(expr);
  instantiate(tmp, current, ns);
  return prop_conv.convert(tmp);
}
