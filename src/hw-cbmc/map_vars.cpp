/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/base_type.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/ebmc_util.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <langapi/language_util.h>
#include <trans-word-level/instantiate_word_level.h>

#include "map_vars.h"
#include "next_timeframe.h"
#include "set_inputs.h"

/*******************************************************************\

Function: instantiate_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_symbol(exprt &expr, unsigned timeframe)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get_identifier();
    symbol_expr.set_identifier(timeframe_identifier(timeframe, identifier));
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    expr.set(ID_identifier, timeframe_identifier(timeframe, identifier));
  }
  else
    Forall_operands(it, expr)
      instantiate_symbol(*it, timeframe);
}

/*******************************************************************\

   Class: map_varst

 Purpose:

\*******************************************************************/

class map_varst:public messaget
{
public:
  map_varst(
    symbol_table_baset &_symbol_table,
    std::list<exprt> &_constraints,
    message_handlert &_message,
    unsigned _no_timeframes)
    : messaget(_message),
      symbol_table(_symbol_table),
      constraints(_constraints),
      no_timeframes(_no_timeframes)
  { }

  void map_vars(const irep_idt &top_module);
  
protected:
  symbol_table_baset &symbol_table;
  std::list<exprt> &constraints;
  unsigned no_timeframes;
  std::set<irep_idt> top_level_inputs;

  symbolt &lookup(const irep_idt &identifier);
  void assign_bound(symbolt &symbol);
  const symbolt &add_array(symbolt &symbol);

  void map_var_rec(
    const irep_idt &top_module,
    const exprt &expr,
    const irep_idt &prefix);

  void map_var(
    const exprt &expr,
    const symbolt &module_symbol);

  void map_var(
    const exprt &program_symbol,
    const symbolt &module_symbol,
    unsigned transition);

  void add_constraint_rec(
    const exprt &program_symbol,
    const exprt &module_symbol);

  bool check_types_rec(
    const typet &type1, const typet &type2,
    std::string &error_msg);

  bool array_types_eq(
    const array_typet &type1, const array_typet &type2,
    std::string &error_msg);
    
  std::string show_member(const exprt &expr);
  void set_transition(exprt &expr, unsigned transition);
  
  mp_integer get_size(const array_typet &type)
  {
    const exprt &size_expr=type.size();

    mp_integer s;
    if(to_integer_non_constant(size_expr, s))
    {
      namespacet ns(symbol_table);
      error() << "failed to convert array size `"
              << from_expr(ns, "", size_expr) << "'" << eom;
      throw 0;
    }
    
    return s;
  }
};

/*******************************************************************\

Function: map_varst::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &map_varst::lookup(const irep_idt &identifier)
{
  auto it = symbol_table.get_writeable(identifier);
  if (it == nullptr) {
    error() << "failed to find identifier `" << identifier
            << "'" << eom;
    throw 0;
  }

  return *it;
}

/*******************************************************************\

Function: map_varst::set_transition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::set_transition(exprt &expr, unsigned transition)
{
  if(expr.id()==ID_member)
  {
    set_transition(to_member_expr(expr).struct_op(), transition);
  }
  else if(expr.id()==ID_index)
  {
    index_exprt &index_expr=to_index_expr(expr);

    assert(index_expr.array().id()==ID_symbol);
    
    symbol_exprt &symbol=to_symbol_expr(index_expr.array());

    // rename that symbol!
    symbol.set_identifier(
      id2string(symbol.get_identifier())+"#0");

    index_expr.index()=from_integer(transition, index_expr.index().type());
  }
}

/*******************************************************************\

Function: is_integral_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static bool is_integral_type(const typet &type)
{
  return type.id()==ID_unsignedbv ||
         type.id()==ID_signedbv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv ||
         type.id()==ID_bool ||
         type.id()==ID_c_bool ||
         type.id()==ID_c_enum_tag;
}

/*******************************************************************\

Function: map_varst::array_types_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool map_varst::array_types_eq(
  const array_typet &type1,
  const array_typet &type2,
  std::string &error_msg)  
{
  mp_integer size1=get_size(type1);
  mp_integer size2=get_size(type2);
    
  // compare sizes
  if(size1!=size2)
  {
    error_msg="array sizes differ ("+
      integer2string(size1)+" vs. "+integer2string(size2)+")";
    return true;
  }
  
  namespacet ns(symbol_table);

  const typet &s1 = ns.follow(type1.element_type());
  const typet &s2 = ns.follow(type2.element_type());

  if(s1.id()==ID_array && s2.id()==ID_array)
    return array_types_eq(to_array_type(s1), to_array_type(s2), error_msg);

  // we are strict: the subtype needs to be identical
  if(!base_type_eq(s1, s2, ns))
  {
    error_msg = "array subtypes differ (E2)";
    return true;
  }
    
  // it's ok
  return false;
}

/*******************************************************************\

Function: map_varst::check_types_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool map_varst::check_types_rec(
  const typet &type1,
  const typet &type2,
  std::string &error_msg)
{
  namespacet ns(symbol_table);

  if(type1.id()==ID_symbol)
    return check_types_rec(ns.follow(type1), type2, error_msg);

  if(type2.id()==ID_symbol)
    return check_types_rec(type1, ns.follow(type2), error_msg);

  // type is the same?
  if(base_type_eq(type1, type2, ns))
    return false;

  // anything between integral types is fine
  if(is_integral_type(type1) && is_integral_type(type2))
    return false;

  if(type1.id()==ID_array)
  {
    if(type2.id()==ID_array)
      return array_types_eq(to_array_type(type1), to_array_type(type2), error_msg);

    // bool-array is mapped to bit-vector
    if(to_array_type(type1).element_type().id() != ID_bool)
    {
      error_msg = "type `" + from_type(ns, "", type1) +
                  "' does not match type `" + from_type(ns, "", type2) +
                  "' (E3)";
      return true;
    }

    if(type2.id()!=ID_unsignedbv &&
       type2.id()!=ID_signedbv)
    {
      error_msg = "type `" + from_type(ns, "", type1) +
                  "' does not match type `" + from_type(ns, "", type2) +
                  "' (E4)";
      return true;
    }

    unsigned width2=to_bitvector_type(type2).get_width();

    mp_integer size1=get_size(to_array_type(type1));

    if(size1!=width2)
    {
      error_msg = "array size (" + integer2string(size1) + ") " +
                  "does not match bit vector size (" +
                   std::to_string(width2) + ") (E5)";
      return 0;
    }
    
    // it's ok
    return false;
  }
  else
  {
    error_msg="can't map program type `"+
              from_type(ns, "", type1)+"'";
    return true;
  }
}

/*******************************************************************\

Function: map_varst::add_constraint_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::add_constraint_rec(
  const exprt &program_symbol,
  const exprt &module_symbol)
{
  namespacet ns(symbol_table);

  const typet &t1=ns.follow(program_symbol.type());
  const typet &t2=ns.follow(module_symbol.type());

  // check the type
  if(t1==t2)
  {
    // the same, ok
    constraints.push_back(
      equal_exprt(program_symbol, module_symbol));
  }
  else
  {
    // we assume that the typecast will work out
    exprt e2_tmp = typecast_exprt{module_symbol, program_symbol.type()};

    constraints.push_back(
      equal_exprt(program_symbol, e2_tmp));
  }
}

/*******************************************************************\

Function: map_varst::map_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::map_var(
  const exprt &program_symbol,
  const symbolt &module_symbol,
  unsigned transition)
{
  // we have s[0].a.b.c
  // make that s#0[transition].a.b.c

  exprt e1=program_symbol;
  set_transition(e1, transition);

  // rhs: symbol
  exprt e2=symbol_exprt(module_symbol.name, module_symbol.type);

  namespacet ns(symbol_table);
  ns.follow_macros(e2);
  instantiate_symbol(e2, transition);
  
  add_constraint_rec(e1, e2);
}

/*******************************************************************\

Function: map_varst::add_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &map_varst::add_array(symbolt &symbol)
{
  const namespacet ns(symbol_table);

  const typet &full_type=ns.follow(symbol.type);

  if(full_type.id()==ID_incomplete_array)
  {
    error() << "`" << symbol.display_name()
            << "' must not be incomplete array" << eom;
    throw 0;
  }

  // add new symbol that is an array
  symbolt new_symbol=symbol;

  exprt array_size=from_integer(no_timeframes, index_type());
  
  array_typet new_type(full_type, array_size);
  
  new_symbol.type=new_type;
  new_symbol.value=exprt(ID_nondet);
  new_symbol.name=id2string(new_symbol.name)+"_array";
  new_symbol.base_name=id2string(new_symbol.base_name)+"_array";

  symbolt *p;
  if(symbol_table.move(new_symbol, p))
    throw "symbol_table.move() failed";
    
  // change initialization
  symbol_exprt symbol_expr(p->type);
  symbol_expr.set_identifier(p->name);
  
  symbol.value=
    index_exprt(symbol_expr, from_integer(0, index_type()), symbol.type);

  return *p;
}

/*******************************************************************\

Function: map_varst::show_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string map_varst::show_member(const exprt &expr)
{
  std::string result;

  if(expr.id()==ID_member)
  {
    result=show_member(to_member_expr(expr).struct_op());
    result+=".";
    result+=id2string(to_member_expr(expr).get_component_name());
  }
  else if(expr.id()==ID_index)
  {
    result=show_member(to_index_expr(expr).array());
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=lookup(to_symbol_expr(expr).get_identifier());
    result=id2string(symbol.display_name());
  }

  return result;
}

/*******************************************************************\

Function: map_varst::map_var_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::map_var_rec(
  const irep_idt &top_module,
  const exprt &expr,
  const irep_idt &prefix)
{
  const namespacet ns(symbol_table);
  const typet &expr_type=ns.follow(expr.type());
  const struct_typet &struct_type=to_struct_type(expr_type);
  const struct_typet::componentst &components=struct_type.components();

  for(struct_typet::componentst::const_iterator
      c_it=components.begin();
      c_it!=components.end();
      c_it++)
  {
    const irep_idt &name=c_it->get_name();
    
    // don't map the struct padding
    if(c_it->get_is_padding()) continue;

    irep_idt base_name;
    
    if(c_it->get_base_name()!=irep_idt())
      base_name=c_it->get_base_name();
    else
      base_name=name;
    
    bool module_instance=ns.follow(c_it->type()).id()==ID_struct;
    
    irep_idt full_name=id2string(prefix)+"."+id2string(base_name);

    const symbol_table_baset::symbolst::const_iterator sub_symbol_it =
      symbol_table.symbols.find(full_name);

    if(sub_symbol_it==symbol_table.symbols.end())
    {
      error() << "mapping failed to find "
              << (module_instance?"module instance":"signal")
              << " `" << full_name << "'" << eom;
      throw 0;
    }
    
    const symbolt &sub_symbol=sub_symbol_it->second;
    
    if(module_instance!=(sub_symbol.type.id()==ID_module_instance))
    {
      error() << "type inconsistency when mapping `" << full_name << "'" << eom;
      throw 0;
    }
    
    member_exprt new_expr(expr, name, c_it->type());
    
    // is it a sub-module or a signal?
    if(module_instance)
    {
      // recursive call
      map_var_rec(top_module, new_expr, full_name);
    }
    else
    {
      // is it a top-level input?
      if(prefix==top_module && sub_symbol.is_input)
        top_level_inputs.insert(name);
      
      // do the mapping of the signal
      map_var(new_expr, sub_symbol);
    }
  }
}
  
/*******************************************************************\

Function: map_varst::map_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::map_var(
  const exprt &program_symbol,
  const symbolt &module_symbol)
{
  // show to user

  status() << "mapping `" << show_member(program_symbol) << "' to `"
           << module_symbol.display_name() << "'" << eom;

  // check types

  const namespacet ns(symbol_table);

  const typet &type1=ns.follow(program_symbol.type());
  const typet &type2=ns.follow(module_symbol.type);

  std::string error_msg;
  if(check_types_rec(type1, type2, error_msg))
  {
    error() <<  "failed to map symbol `" << show_member(program_symbol)
            << "' because: " << error_msg << eom;
    throw 0;
  }
      
  // map values

  for(unsigned t=0; t<no_timeframes; t++)
    map_var(program_symbol, module_symbol, t);
}

/*******************************************************************\

Function: map_varst::assign_bound

  Inputs:

 Outputs:

 Purpose: Assign bound to external ANSI-C symbols

\*******************************************************************/

void map_varst::assign_bound(symbolt &symbol)
{
  if(!symbol.is_extern)
  {
    error() << "symbol `" << symbol.display_name()
            << "' should be extern" << eom;
    throw 0;
  }

  symbol.value=from_integer(no_timeframes-1, symbol.type);
  symbol.is_extern=false;
}

/*******************************************************************\

Function: map_varst::map_vars

  Inputs:

 Outputs:

 Purpose: Looks through symbol_table for external ANSI-C symbols
          Calls map_var to find mapping to HDL

\*******************************************************************/

void map_varst::map_vars(const irep_idt &top_module)
{
  // add timeframe symbol
  {
    symbolt timeframe_symbol;

    timeframe_symbol.base_name="timeframe";
    timeframe_symbol.name="hw-cbmc::timeframe";
    timeframe_symbol.type=index_type();
    timeframe_symbol.is_static_lifetime=true;
    timeframe_symbol.is_lvalue=true;
    timeframe_symbol.value=from_integer(0, index_type());

    symbol_table.add(timeframe_symbol);
  }

  const symbolt &top_module_symbol=lookup(top_module);
  
  irep_idt struct_symbol;

  for (auto &entry : symbol_table) {
    symbolt &symbol = symbol_table.get_writeable_ref(entry.first);
    if (symbol.mode == ID_C || symbol.mode == ID_cpp) {
      const irep_idt &base_name = symbol.base_name;

      if (symbol.is_static_lifetime) {
        if (base_name == "bound") // special case
          assign_bound(symbol);
        else if(base_name==top_module_symbol.base_name)
          struct_symbol = entry.first;
      }
    }
  }
  
  if(struct_symbol=="")
  {
    error() << "failed to find top-module symbol `"
            << top_module_symbol.base_name << "'" << eom;
    return;
  }

  namespacet ns(symbol_table);

  {
    symbolt &s=lookup(struct_symbol);
    
    if(!s.is_extern)
    {
      error() << "symbol `" << s.display_name()
              << "' should be extern" << eom;
      throw 0;
    }

    const symbolt &array_symbol=add_array(s);

    symbol_exprt symbol_expr(array_symbol.type);
    symbol_expr.set_identifier(array_symbol.name);

    exprt timeframe_expr=from_integer(0, index_type());

    index_exprt expr(
      symbol_expr,
      timeframe_expr,
      to_array_type(ns.follow(symbol_expr.type())).element_type());

    top_level_inputs.clear();

    map_var_rec(top_module_symbol.name, expr, id2string(top_module_symbol.name));
  }

  for (const auto &entry : symbol_table) {
    if (entry.second.mode == ID_C || entry.second.mode == ID_cpp) {
      const irep_idt &base_name = entry.second.base_name;
      symbolt &symbol = symbol_table.get_writeable_ref(entry.first);
      if (symbol.type.id() == ID_struct_tag)
        symbol.type = ns.follow(symbol.type);
      if (base_name == "next_timeframe" && symbol.type.id() == ID_code) {
        namespacet ns(symbol_table);
        add_next_timeframe(symbol, struct_symbol, top_level_inputs, ns);
      } else if (base_name == "set_inputs" && symbol.type.id() == ID_code) {
        namespacet ns(symbol_table);
        add_set_inputs(symbol, struct_symbol, top_level_inputs, ns);
      }
    }
  }
}

/*******************************************************************\

Function: map_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_vars(
  symbol_table_baset &symbol_table,
  const irep_idt &module,
  std::list<exprt> &constraints,
  message_handlert &message,
  unsigned no_timeframes)
{
  map_varst map_vars(symbol_table, constraints, message, no_timeframes);
  map_vars.map_vars(module);
}
