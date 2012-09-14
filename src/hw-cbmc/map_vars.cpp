/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <i2string.h>
#include <arith_tools.h>
#include <namespace.h>
#include <config.h>
#include <base_type.h>
#include <std_expr.h>
#include <std_code.h>
#include <message_stream.h>

#include <langapi/language_util.h>
#include <ansi-c/c_types.h>
#include <trans/instantiate.h>

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
  if(expr.id()==ID_symbol ||
     expr.id()==ID_nondet_symbol)
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

class map_varst:public message_streamt
{
public:
  map_varst(contextt &_context, expr_listt &_constraints,
            message_handlert &_message, unsigned _no_timeframes):
    message_streamt(_message),
    context(_context), constraints(_constraints),
    no_timeframes(_no_timeframes)
  { }

  void map_vars(const irep_idt &module);
  
protected:
  contextt &context;
  expr_listt &constraints;
  unsigned no_timeframes;
  std::set<irep_idt> top_level_inputs;

  symbolt &lookup(const irep_idt &identifier);
  void assign_bound(symbolt &symbol);
  const symbolt &add_array(symbolt &symbol);

  void map_var_rec(
    const irep_idt &main_module,
    const exprt &expr,
    const symbolt::hierarchyt &hierarchy);

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
    if(to_integer(size_expr, s))
    {
      namespacet ns(context);
      str << "failed to convert array size `"
          << from_expr(ns, "", size_expr) << "'";
      error();
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
  contextt::symbolst::iterator it=
    context.symbols.find(identifier);

  if(it==context.symbols.end())
  {
    str << "failed to find identifier `" << identifier
        << "'";
    error();
    throw 0;
  }

  return it->second;
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
    if(expr.operands().size()!=1)
      throw "member expected to have one operand";

    set_transition(expr.op0(), transition);
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";
      
    assert(expr.op0().id()==ID_symbol);

    // rename!
    expr.op0().set(ID_identifier,
      expr.op0().get_string(ID_identifier)+"#0");

    expr.op1()=from_integer(transition, expr.op1().type());
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
         type.id()==ID_bool;
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
  
  namespacet ns(context);
  
  const typet &s1=ns.follow(type1.subtype());
  const typet &s2=ns.follow(type2.subtype());
  
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
  namespacet ns(context);

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
    if(type1.subtype().id()!=ID_bool)
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
                   i2string(width2) + ") (E5)";
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
  namespacet ns(context);

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
    exprt e2_tmp=module_symbol;
    e2_tmp.make_typecast(program_symbol.type());

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

  namespacet ns(context);
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
  const namespacet ns(context);

  const typet &full_type=ns.follow(symbol.type);

  if(full_type.id()==ID_incomplete_array)
  {
    str << "`" << symbol.display_name() << "' must not be incomplete array";
    error();
    throw 0;
  }

  // add new symbol that is an array
  symbolt new_symbol=symbol;

  exprt array_size=from_integer(no_timeframes, index_type());
  
  array_typet new_type;
  new_type.size()=array_size;
  new_type.subtype()=full_type;
  
  new_symbol.type=new_type;
  new_symbol.value=exprt(ID_nondet);
  new_symbol.name=id2string(new_symbol.name)+"_array";
  new_symbol.base_name=id2string(new_symbol.base_name)+"_array";

  symbolt *p;
  if(context.move(new_symbol, p))
    throw "context.move() failed";
    
  // change initialization
  exprt symbol_expr(ID_symbol, p->type);
  symbol_expr.set(ID_identifier, p->name);
  
  symbol.value=exprt(ID_index, symbol.type);
  symbol.value.copy_to_operands(symbol_expr, gen_zero(index_type()));

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
    if(expr.operands().size()!=1)
      throw "member expected to have one operand";

    result=show_member(expr.op0());
    result+=".";
    result+=expr.get_string(ID_component_name);
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";

    result=show_member(expr.op0());
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=lookup(expr.get(ID_identifier));
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
  const irep_idt &main_module,
  const exprt &expr,
  const symbolt::hierarchyt &hierarchy)
{
  const namespacet ns(context);
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
    
    std::list<const symbolt *> symbols;

    forall_symbol_module_map(s_it, context.symbol_module_map, main_module)
    {
      const symbolt &s=lookup(s_it->second);
      if(s.type.id()==ID_module) continue;
      if(s.base_name==base_name &&
         hierarchy==s.hierarchy &&
         module_instance==(s.type.id()==ID_module_instance))
      {
        symbols.push_back(&s);
      }
    }
    
    if(symbols.empty())
    {
      str << "failed to find `" << base_name << "' in module `"
          << show_member(expr) << "'";
      error();
      throw 0;
    }

    exprt new_expr(ID_member, c_it->type());
    new_expr.copy_to_operands(expr);
    new_expr.set(ID_component_name, name);
    
    const symbolt &module_symbol=**symbols.begin();
    
    // is it another module?
    if(module_symbol.type.id()==ID_module_instance)
    {
      symbolt::hierarchyt new_hierarchy(hierarchy);
      new_hierarchy.push_back(module_symbol.name);
    
      // recursive call
      map_var_rec(main_module, new_expr, new_hierarchy);
    }
    else
    {
      // is it a top-level input?
      if(hierarchy.empty() && module_symbol.is_input)
        top_level_inputs.insert(name);
      
      // do the mapping    
      map_var(new_expr, module_symbol);
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

  str << "mapping `" << show_member(program_symbol) << "' to `"
      << module_symbol.display_name() << "'";
  status();

  // check types

  const namespacet ns(context);

  const typet &type1=ns.follow(program_symbol.type());
  const typet &type2=ns.follow(module_symbol.type);

  std::string error_msg;
  if(check_types_rec(type1, type2, error_msg))
  {
    str << "failed to map symbol `" << show_member(program_symbol)
        << "' because: " << error_msg;
    error();
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
    str << "symbol `" << symbol.display_name() << "' should be extern";
    error();
    throw 0;
  }

  symbol.value=from_integer(no_timeframes-1, symbol.type);
  symbol.is_extern=false;
}

/*******************************************************************\

Function: map_varst::map_vars

  Inputs:

 Outputs:

 Purpose: Looks through context for external ANSI-C symbols
          Calls map_var to find mapping to HDL

\*******************************************************************/

void map_varst::map_vars(const irep_idt &module)
{
  // add timeframe symbol
  {
    symbolt timeframe_symbol;

    timeframe_symbol.base_name="timeframe";
    timeframe_symbol.name="hw-cbmc::timeframe";
    timeframe_symbol.type=index_type();
    timeframe_symbol.static_lifetime=true;
    timeframe_symbol.lvalue=true;
    timeframe_symbol.value=gen_zero(index_type());

    context.move(timeframe_symbol);
  }

  const symbolt &module_symbol=lookup(module);
  
  irep_idt struct_symbol;
  
  Forall_symbols(it, context.symbols)
  {
    if(it->second.mode==ID_C ||
       it->second.mode==ID_cpp ||
       it->second.mode==ID_SpecC)
    {
      const irep_idt &base_name=it->second.base_name;

      if(it->second.static_lifetime)
      {
        if(base_name=="bound") // special case      
          assign_bound(it->second);
        else if(base_name==module_symbol.base_name)
          struct_symbol=it->first;
      }
    }
  }
  
  if(struct_symbol=="")
  {
    std::string text=
      "failed to find top-module symbol `"+
      id2string(module_symbol.base_name)+"'";
    error(text);
    return;
  }
  
  {
    symbolt &s=lookup(struct_symbol);
    
    if(!s.is_extern)
    {
      str << "symbol `" << s.display_name() << "' should be extern";
      error();
      throw 0;
    }

    const symbolt &array_symbol=add_array(s);

    exprt symbol_expr(ID_symbol, array_symbol.type);
    symbol_expr.set(ID_identifier, array_symbol.name);

    exprt timeframe_expr=from_integer(0, index_type());

    namespacet ns(context);
    exprt expr(ID_index, ns.follow(symbol_expr.type()).subtype());
    expr.move_to_operands(symbol_expr, timeframe_expr);

    top_level_inputs.clear();

    symbolt::hierarchyt hierarchy;
    map_var_rec(module_symbol.name, expr, hierarchy);
  }

  Forall_symbols(it, context.symbols)
  {
    if(it->second.mode==ID_C ||
       it->second.mode==ID_cpp ||
       it->second.mode==ID_SpecC)
    {
      const irep_idt &base_name=it->second.base_name;

      if(base_name=="next_timeframe" &&
         it->second.type.id()==ID_code)
      {
        namespacet ns(context);
        add_next_timeframe(it->second, struct_symbol, top_level_inputs, ns);
      }
      else if(base_name=="set_inputs" &&
              it->second.type.id()==ID_code)
      {
        namespacet ns(context);
        add_set_inputs(it->second, struct_symbol, top_level_inputs, ns);
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
  contextt &context,
  const irep_idt &module,
  expr_listt &constraints,
  message_handlert &message,
  unsigned no_timeframes)
{
  map_varst map_vars(context, constraints, message, no_timeframes);
  map_vars.map_vars(module);
}
