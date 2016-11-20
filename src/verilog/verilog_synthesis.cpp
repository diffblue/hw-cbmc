/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <map>
#include <set>

#include <util/i2string.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/identifier.h>
#include <util/std_expr.h>

#include "expr2verilog.h"
#include "verilog_synthesis.h"
#include "verilog_synthesis_class.h"
#include "verilog_expr.h"

/*******************************************************************\

Function: verilog_synthesist::synth_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_expr(
  exprt &expr,
  symbol_statet symbol_state)
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=lookup(to_symbol_expr(expr));
    
    // does it have a value?
    valuest::const_iterator v_it=values.find(symbol.name);

    if(v_it!=values.end())
    {
      exprt c=from_integer(v_it->second, integer_typet());
      c.add_source_location()=expr.source_location();
      expr=c;
    }
    else if(symbol.is_macro)
    {
      // substitute
      assert(symbol.value.is_not_nil());
      expr=symbol.value;
      
      // recursive call
      synth_expr(expr, symbol_state);
    }
    else
    {
      switch(symbol_state)
      {
      case symbol_statet::SYMBOL:
        break;

      case symbol_statet::CURRENT:
        expr=current_value(symbol);
        break;

      case symbol_statet::FINAL:
        expr=final_value(symbol);
        break;

      case symbol_statet::NONE:
        error().source_location=expr.source_location();
        error() << "symbols not allowed here" << eom;
        throw 0;
      }
    }
  }
  else if(expr.id()==ID_function_call)
  {
    expand_function_call(to_function_call_expr(expr));
  }
  else if(expr.id()==ID_hierarchical_identifier)
  {
    expand_hierarchical_identifier(
      to_hierarchical_identifier_expr(expr),
      symbol_state);
  }
  else if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    synth_expr(expr.op0(), symbol_state);

    // we perform some form of simplification for these
    if(expr.op0().is_constant())
      simplify(expr, ns);
  }
  else if(expr.has_operands())
    Forall_operands(it, expr)
      synth_expr(*it, symbol_state);   
}

/*******************************************************************\

Function: verilog_synthesist::expand_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::expand_function_call(function_call_exprt &call)
{
  // check some restrictions
  if(construct!=constructt::INITIAL &&
     construct!=constructt::ALWAYS)
  {
    error().source_location=call.source_location();
    error() << "function call not allowed here" << eom;
    throw 0;
  }

  // this is essentially inlined
  const symbol_exprt &function=to_symbol_expr(call.function());
  
  const symbolt &symbol=lookup(function);
  
  if(symbol.type.id()!=ID_code)
  {
    error().source_location=call.source_location();
    error() << "function call expects function argument" << eom;
    throw 0;
  }
  
  const code_typet &code_type=to_code_type(symbol.type);

  if(code_type.return_type()==empty_typet())
  {
    error().source_location=call.source_location();
    error() << "function call cannot call task" << eom;
    throw 0;
  }
  
  const code_typet::parameterst &parameters=
    code_type.parameters();
    
  const exprt::operandst &actuals=
    call.op1().operands();
    
  if(parameters.size()!=actuals.size())
  {
    error().source_location=call.source_location();
    error() << "wrong number of arguments" << eom;
    throw 0;
  }
  
  // do assignments to function parameters
  for(unsigned i=0; i<parameters.size(); i++)
  {
    const symbolt &a_symbol=lookup(parameters[i].get_identifier());
    verilog_blocking_assignt assignment;
    assignment.lhs()=a_symbol.symbol_expr();
    assignment.rhs()=actuals[i];
    assignment.add_source_location()=call.source_location();
    synth_statement(assignment);
  }

  synth_statement(to_verilog_statement(symbol.value));
  
  // replace function call by return value symbol
  const symbolt &return_symbol=
    lookup(id2string(symbol.name)+"."+
           id2string(symbol.base_name));

  exprt return_value=return_symbol.symbol_expr();

  call.swap(return_value);
}

/*******************************************************************\

Function: verilog_synthesist::expand_hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::expand_hierarchical_identifier(
  hierarchical_identifier_exprt &expr,
  symbol_statet symbol_state)
{
  synth_expr(expr.op0(), symbol_state);

  if(expr.op0().id()!=ID_symbol)
  {
    error().source_location=expr.source_location();
    error() << "synthesis expected symbol on lhs of `.'" << eom;
    throw 0;
  }

  if(expr.op0().type().id()!=ID_module_instance)
  {
    error().source_location=expr.source_location();
    error() << "synthesis expected module instance on lhs of `.', but got `"
            << to_string(expr.op0().type()) << '\'' << eom;
    throw 0;
  }
  
  const irep_idt &lhs_identifier=expr.op0().get(ID_identifier);

  // rhs

  if(expr.op1().id()!=ID_symbol)
  {
    error().source_location=expr.source_location();
    error() << "synthesis expected symbol on rhs of `.', but got `"
            << to_string(expr.op1()) << '\'' << eom;
    throw 0;
  }

  const irep_idt &rhs_identifier=expr.op1().get(ID_identifier);

  // just patch together
  
  std::string full_identifier=
    id2string(lhs_identifier)+"."+id2string(rhs_identifier);

  // Note: may not yet be in symbol table, as the inst module
  // item may be later.
  // The type checker already checked that it's fine.

  symbol_exprt new_symbol;
  new_symbol.type()=expr.type();
  new_symbol.add_source_location()=expr.source_location();
  new_symbol.set_identifier(full_identifier);
  expr.swap(new_symbol);
}

/*******************************************************************\

Function: verilog_synthesist::assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::assignment(
  const exprt &lhs,
  const exprt &rhs,
  bool blocking)
{
  if(lhs.id()==ID_concatenation) // split it up                                
  {
    // TODO: split it up more intelligently;
    // bit-wise is wasteful.
    unsigned offset=0;
    
    // do it from right to left
    
    for(exprt::operandst::const_reverse_iterator
        it=lhs.operands().rbegin();
        it!=lhs.operands().rend();
        it++)
    {
      constant_exprt offset_constant;
      offset_constant.type()=natural_typet();
      offset_constant.set(ID_value, offset);

      if(it->type().id()==ID_bool)
      {
        exprt bit_extract(ID_extractbit, it->type());
        bit_extract.copy_to_operands(rhs, offset_constant);
        offset++;

        assignment(*it, bit_extract, blocking);
      }
      else if(it->type().id()==ID_signedbv ||
              it->type().id()==ID_unsignedbv)
      {
        unsigned width=get_width(it->type());
      
        constant_exprt offset_constant2;
        offset_constant2.type()=natural_typet();
        offset_constant2.set(ID_value, offset+width-1);

        extractbits_exprt bit_extract(
          rhs, offset_constant, offset_constant2, it->type());
        
        assignment(*it, bit_extract, blocking);
        
        offset+=width;
      }
      else
      {
        error().source_location=it->source_location();
        error() << "assignment to type `" << to_string(it->type())
                << "' not supported" << eom;
      }
    }
    
    return;
  }
  
  // get identifier
  const symbolt &symbol=assignment_symbol(lhs);
  
  if(symbol.type.id()==ID_verilog_realtime)
  {
    // we silently ignore these
    return;
  }
  
  if(!symbol.is_state_var)
  {
    error().source_location=lhs.source_location();
    error() << "assignment to non-register" << eom;
    throw 0;
  }

  if(construct==constructt::ALWAYS &&
     event_guard==event_guardt::NONE)
  {
    error().source_location=lhs.source_location();
    error() << "permanent assignment without event guard" << eom;
    throw 0;
  }

  {
    event_guardt new_type;

    if(construct==constructt::ALWAYS)  
      new_type=event_guard;
    else
      new_type=event_guardt::CLOCK;
      
    assignmentt &assignment=assignments[symbol.name];

    if(assignment.type==event_guardt::NONE)
      assignment.type=new_type;
    else if(assignment.type!=new_type)
    {
      error().source_location=lhs.source_location();
      error() << "conflicting assignment types for `"
              << symbol.base_name
              << "' (new: "
              << as_string(new_type) << ", old: "
              << as_string(assignment.type) << ")" << eom;
      throw 0;      
    }
    
    membert member;
    assignment_member_rec(lhs, member,
      (construct==constructt::INITIAL)?assignment.init:assignment.next);
  }

  {
    assert(value_map!=NULL);

    exprt new_rhs(rhs), new_value;
    assignment_rec(lhs, new_rhs, new_value); // start of recursion

    // These can explode if the symbol is assigned more than once
    // and also used more than once, e.g., in a multi-dimensional array.
    // We add a fresh symbol for anything that is not trivial
    // to prevent that.
    if(new_value.id()!=ID_symbol &&
       new_value.id()!=ID_constant)
    {
      replace_by_wire(new_value, symbol);
    }

    if(blocking)
      value_map->current.assign(symbol.name, new_value);

    value_map->final.assign(symbol.name, new_value);
  }
}

/*******************************************************************\

Function: verilog_synthesist::assignment_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::assignment_rec(
  const exprt &lhs,
  exprt &rhs,
  exprt &new_value)
{
  if(lhs.id()==ID_symbol)
  {
    new_value.swap(rhs);
    rhs.clear();
  }
  else if(lhs.id()==ID_index ||
          lhs.id()==ID_extractbit)
  {
    if(lhs.operands().size()!=2)
    {
      error() << "index takes two operands" << eom;
      throw 0;
    }

    const exprt &lhs_array = lhs.op0();
    const exprt &lhs_index = lhs.op1();

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    exprt new_rhs(ID_with, lhs_array.type());

    new_rhs.reserve_operands(3);
    new_rhs.copy_to_operands(lhs_array);
    new_rhs.copy_to_operands(lhs_index);
    new_rhs.move_to_operands(rhs);

    // do the array
    synth_expr(new_rhs.op0(), symbol_statet::FINAL);

    // do the index
    synth_expr(new_rhs.op1(), symbol_statet::CURRENT);
    
    // do the value
    assignment_rec(lhs_array, new_rhs, new_value); // recursive call
  }
  else if(lhs.id()==ID_extractbits)
  {
    // we flatten n-bit extractbits into n times extractbit

    if(lhs.operands().size()!=3)
    {
      error() << "extractbits takes three operands" << eom;
      throw 0;
    }

    const exprt &lhs_bv        = lhs.op0();
    const exprt &lhs_index_one = lhs.op1();
    const exprt &lhs_index_two = lhs.op2();

    mp_integer from, to;

    if(to_integer(lhs_index_one, from))
    {
      error().source_location=lhs_index_one.source_location();
      error() << "failed to convert range" << eom;
      throw 0;
    }

    if(to_integer(lhs_index_two, to))
    {
      error().source_location=lhs_index_two.source_location();
      error() << "failed to convert range" << eom;
      throw 0;
    }

    if(from>to)
      std::swap(from, to);

    // redundant?
    if(from==0 &&
       to==get_width(lhs_bv.type())-1)
    {
      assignment_rec(lhs_bv, rhs, new_value); // recursive call
      return;
    }

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    exprt synth_lhs_bv(lhs_bv);

    // do the array, but just once
    synth_expr(synth_lhs_bv, symbol_statet::FINAL);

    exprt last_value;
    last_value.make_nil();

    // now add the indexes in the range
    for(mp_integer i=from; i<=to; ++i)
    {
      exprt offset=from_integer(i-from, integer_typet());

      exprt rhs_extractbit(ID_extractbit, bool_typet());
      rhs_extractbit.reserve_operands(2);
      rhs_extractbit.copy_to_operands(rhs);
      rhs_extractbit.move_to_operands(offset);

      exprt count=from_integer(i, integer_typet());

      exprt new_rhs(ID_with, lhs_bv.type());
      new_rhs.reserve_operands(3);
      new_rhs.copy_to_operands(synth_lhs_bv);
      new_rhs.move_to_operands(count);
      new_rhs.move_to_operands(rhs_extractbit);

      // do the value
      assignment_rec(lhs_bv, new_rhs, new_value); // recursive call

      if(last_value.is_nil())
        last_value.swap(new_value);
      else
      {
        // merge the withs
        assert(new_value.id()==ID_with);
        assert(new_value.operands().size()==3);
        assert(last_value.id()==ID_with);
        assert(last_value.operands().size()>=3);

        last_value.move_to_operands(new_value.op1());
        last_value.move_to_operands(new_value.op2());
      }
    }

    new_value.swap(last_value);
  }
  else
  {
    error() << "unexpected lhs: "+lhs.id_string() << eom;
    throw 0;
  }

  #if 0
  // do "with" merging

  if(new_value.id()==ID_with &&
     new_value.op0().id()==ID_with)
  {
    exprt tmp;

    tmp.swap(new_value.op0());

    tmp.reserve_operands(tmp.operands().size()+2);
    tmp.move_to_operands(new_value.op1());
    tmp.move_to_operands(new_value.op2());

    new_value.swap(tmp);
  }
  #endif
}

/*******************************************************************\

Function: verilog_synthesist::replace_by_wire
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::replace_by_wire(
  exprt &what,
  const symbolt &base)
{
  symbolt new_symbol;
  
  do
  {
    unsigned c=temporary_counter++;
    new_symbol.name=id2string(base.name)+"_aux"+i2string(c);
    new_symbol.base_name=id2string(base.base_name)+"_aux"+i2string(c);
  }
  while(symbol_table.symbols.find(new_symbol.name)!=symbol_table.symbols.end());
  
  new_symbol.type=what.type();
  new_symbol.module=base.module;
  new_symbol.mode=base.mode;
  new_symbol.location=base.location;
  new_symbol.value=nil_exprt();
  new_symbol.is_auxiliary=true;

  symbol_exprt symbol_expr(new_symbol.name, new_symbol.type);

  assignmentt &assignment=assignments[new_symbol.name];
  assignment.next.value=what;
  new_wires.insert(new_symbol.name);
  
  if(symbol_table.move(new_symbol))
  {
    error() << "failed to add replace_by_wire symbol" << eom;
    throw 0;
  }
    
  what=symbol_expr;
}

/*******************************************************************\

Function: verilog_synthesist::assignment_member_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::assignment_member_rec(
  const exprt &lhs,
  membert &member,
  assignmentt::datat &data)
{
  if(lhs.id()==ID_symbol)
  {
    // done
    add_assignment_member(lhs, member, data);
  }
  else if(lhs.id()==ID_index ||
          lhs.id()==ID_extractbit)
  {
    if(lhs.operands().size()!=2)
    {
      error() << "index takes two operands" << eom;
      throw 0;
    }
    
    exprt tmp_lhs_op1=simplify_expr(lhs.op1(), ns);
      
    // constant index?
    mp_integer index;
    if(to_integer(tmp_lhs_op1, index))
    {
      // done
      add_assignment_member(lhs, member, data);
    }
    else
    {
      // do the value
      member.push_back(index);
      assignment_member_rec(lhs.op0(), member, data);
      member.pop_back();
    }
  }
  else if(lhs.id()==ID_extractbits)
  {
    // we flatten n-bit extractbits into n times extractbit

    if(lhs.operands().size()!=3)
    {
      error() << "extractbits takes three operands" << eom;
      throw 0;
    }

    const exprt &lhs_bv        = lhs.op0();
    const exprt &lhs_index_one = lhs.op1();
    const exprt &lhs_index_two = lhs.op2();

    mp_integer from, to;

    if(to_integer(lhs_index_one, from))
    {
      error().source_location=lhs_index_one.source_location();
      error() << "failed to convert range" << eom;
      throw 0;
    }

    if(to_integer(lhs_index_two, to))
    {
      error().source_location=lhs_index_two.source_location();
      error() << "failed to convert range" << eom;
      throw 0;
    }

    if(from>to)
      std::swap(from, to);

    member.push_back(mp_integer());

    // now add the indexes in the range
    for(mp_integer i=from; i<=to; ++i)
    {
      // do the value
      member.back()=i;
      assignment_member_rec(lhs_bv, member, data);
    }
    
    member.pop_back();
  }
  else
  {
    error() << "unexpected lhs: "+lhs.id_string() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_synthesist::disjoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_synthesist::disjoint(
  const membert &a,
  const membert &b)
{
  membert::const_iterator a_it=a.begin();
  membert::const_iterator b_it=b.begin();
  
  while(a_it!=a.end() && b_it!=b.end())
  {
    if(*a_it!=*b_it) return true;
    a_it++, b_it++;
  }
  
  return false;
}

/*******************************************************************\

Function: verilog_synthesist::add_assignment_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::add_assignment_member(
  const exprt &lhs,
  const membert &member,
  assignmentt::datat &data)
{
  // see if we conflict with any previous assignment
  for(const auto & it : data.assigned_previous)
  {
    if(!disjoint(member, it))
    {
      error().source_location=lhs.source_location();
      error() << "conflict with previous assignment" << eom;
      throw 0;
    }
  }

  data.assigned_current.push_back(member);
}

/*******************************************************************\

Function: verilog_synthesist::assignment_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &verilog_synthesist::assignment_symbol(const exprt &lhs)
{
  const exprt *e=&lhs;

  while(1)
  {
    if(e->id()==ID_index)
    {
      if(e->operands().size()!=2)
      {
        error() << "index takes two operands" << eom;
        throw 0;
      }
        
      e=&e->op0();
      
      if(e->type().id()!=ID_array)
      {
        error() << "index expects array operand" << eom;
        throw 0;
      }
    }
    else if(e->id()==ID_extractbit)
    {
      if(e->operands().size()!=2)
      {
        error() << "extractbit takes two operands" << eom;
        throw 0;
      }

      e=&e->op0();
    }
    else if(e->id()==ID_extractbits)
    {
      if(e->operands().size()!=3)
      {
        error() << "extractbits takes three operands" << eom;
        throw 0;
      }

      e=&e->op0();
    }
    else if(e->id()==ID_symbol)
    {
      // get identifier

      const irep_idt &identifier=e->get(ID_identifier);

      symbol_tablet::symbolst::iterator it=
        symbol_table.symbols.find(identifier);

      if(it==symbol_table.symbols.end())
      {
        error() << "assignment failed to find symbol `"
                << identifier
                << '\'' << eom;
        throw 0;
      }

      return it->second;
    }
    else
    {
      error() << "synthesis: failed to get identifier" << eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::replace_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_synthesist::replace_symbols(
  const replace_mapt &what,
  exprt &dest)
{
  bool result=true;

  if(dest.id()==ID_next_symbol ||
     dest.id()==ID_symbol)
  {
    replace_mapt::const_iterator it=
      what.find(dest.get(ID_identifier));

    if(it!=what.end())
    {
      bool is_next_symbol=dest.id()==ID_next_symbol;
      dest=it->second;      

      if(is_next_symbol)
        replace_symbols(ID_next_symbol, dest);

      result=false;
    }
  }
  else
  {
    Forall_operands(it, dest)
      result=replace_symbols(what, *it) && result;
  }

  return result;
}

/*******************************************************************\

Function: verilog_synthesist::replace_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::replace_symbols(
  const irep_idt &target,
  exprt &dest)
{
  if(dest.id()==ID_symbol)
    dest.id(target);
  else
    Forall_operands(it, dest)
      replace_symbols(target, *it);
}

/*******************************************************************\

Function: verilog_synthesist::instantiate_port

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::instantiate_port(
  const exprt &symbol_expr,
  const exprt &value,
  const replace_mapt &replace_map,
  transt &trans)
{
  irep_idt identifier=symbol_expr.get(ID_identifier);

  replace_mapt::const_iterator it=
    replace_map.find(identifier);

  if(it==replace_map.end())
  {
    error() << "failed to find " << identifier << " in replace_map"
            << eom;
    throw 0;
  }

  equal_exprt equality(it->second, value);

  if(equality.op0().type()!=equality.op1().type())
    equality.op0().make_typecast(equality.op1().type());

  trans.invar().move_to_operands(equality);
}

/*******************************************************************\

Function: verilog_synthesist::instantiate_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::instantiate_ports(
  const irep_idt &instance,
  const exprt &inst,
  const symbolt &symbol,
  const replace_mapt &replace_map,
  transt &trans)
{
  const irept::subt &ports=symbol.type.find(ID_ports).get_sub();

  if(inst.operands().size()==0)
    return;

  // named port connection?

  if(inst.op0().id()==ID_named_port_connection)
  {
    // no requirement that all ports are connected
    forall_operands(o_it, inst)
    {
      if(o_it->operands().size()==2)
      {
        const exprt &op0=o_it->op0();
        const exprt &op1=o_it->op1();

        if(op1.is_not_nil())
          instantiate_port(op0, op1, replace_map, trans);
      }
    }
  }
  else // just a list without names
  {
    if(inst.operands().size()!=ports.size())
    {
      error().source_location=inst.source_location();
      error() << "wrong number of ports: expected " << ports.size() 
              << " but got " << inst.operands().size() << eom;
      throw 0;
    }

    irept::subt::const_iterator p_it=
      ports.begin();

    forall_operands(o_it, inst)
    {
      instantiate_port((exprt &)(*p_it), *o_it,
                       replace_map, trans);
      p_it++;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_module_instance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_module_instance(
  const verilog_instt &statement,
  transt &trans)
{
  const irep_idt &identifier=statement.get_module();

  // must be in symbol_table
  const symbolt &symbol=lookup(identifier);
  
  // make sure it's synthesized already
  verilog_synthesis(
    symbol_table, identifier, get_message_handler(), options);

  forall_operands(it, statement)
    expand_module_instance(symbol, *it, trans);
}

/*******************************************************************\

Function: verilog_synthesist::synth_module_instance_builtin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_module_instance_builtin(
  const verilog_inst_builtint &module_item,
  transt &trans)
{
  const irep_idt &module=module_item.get_module();

  forall_operands(it, module_item)
  {
    const exprt &instance=*it;

    // check built-in ones
    if(module==ID_bufif0 ||
       module==ID_bufif1 ||
       module==ID_notif0 ||
       module==ID_notif1)
    {
      // add to general constraints
    
      exprt constraint=*it;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().move_to_operands(constraint);
    }
    else if(module==ID_nmos ||
            module==ID_pmos ||
            module==ID_rnmos ||
            module==ID_rpmos)
    {
      // add to general constraints
    
      exprt constraint=*it;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().move_to_operands(constraint);
    }
    else if(module==ID_and ||
            module==ID_nand ||
            module==ID_or ||
            module==ID_nor ||
            module==ID_xor ||
            module==ID_xnor)
    {
      assert(instance.operands().size()>=2);

      if(instance.operands().size()==2)
      {
        equal_exprt constraint;
        constraint.lhs()=instance.operands()[0];
        constraint.rhs()=instance.operands().back();
        trans.invar().move_to_operands(constraint);
      }
      else
      {
        for(unsigned i=1; i<=instance.operands().size()-2; i++)
        {
          exprt op(module, instance.type());

          if(i==1)
            op.copy_to_operands(instance.operands()[i],
                                instance.operands()[i+1]);
          else
            op.copy_to_operands(instance.operands()[0],
                                instance.operands()[i+1]);

          if(instance.type().id()!=ID_bool)
            op.id("bit"+op.id_string());

          equal_exprt constraint(instance.op0(), op);
          assert(trans.operands().size()==3);
          trans.invar().move_to_operands(constraint);
        }
      }
      
      /*assert(instance.operands().size()!=3);      
      op.move_to_operands(instance.op1(), instance.op2());
      
      if(instance.type().id()!=ID_bool)
        op.id("bit"+op.id_string());
      
      equal_exprt constraint(instance.op0(), op);
    
      assert(trans.operands().size()!=3);
      trans.invar().move_to_operands(constraint);
      */
    }
    else if(module==ID_buf)
    {
      assert(instance.operands().size()>=2);

      for(unsigned i=0; i<instance.operands().size()-1; i++)
      {
        equal_exprt constraint;
        constraint.lhs()=instance.operands()[i];
        constraint.rhs()=instance.operands().back();
    
        assert(trans.operands().size()==3);
        trans.invar().move_to_operands(constraint);
      }
    }
    else if(module==ID_not)
    {
      assert(instance.operands().size()>=2);

      for(unsigned i=0; i<instance.operands().size()-1; i++)
      {
        exprt op(ID_not, instance.type());
        op.copy_to_operands(instance.operands()[i]);
      
        if(instance.type().id()!=ID_bool)
          op.id("bit"+op.id_string());
      
        equal_exprt constraint;
        constraint.lhs()=op;
        constraint.rhs()=instance.operands().back();
    
        assert(trans.operands().size()==3);
        trans.invar().move_to_operands(constraint);
      }
    }
    else if(module=="tranif0" ||
            module=="tranif1" ||
            module=="rtranif1" ||
            module=="rtranif0")
    {
      // add to general constraints
    
      exprt constraint=*it;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().move_to_operands(constraint);
    }
    else if(module=="tran"  ||
            module=="rtran")
    {
      // add to general constraints
    
      exprt constraint=*it;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().move_to_operands(constraint);
    }
    else
    {
      error().source_location=module_item.source_location();
      error() << "do not know how to synthesize " << module << eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::expand_module_instance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::expand_module_instance(
  const symbolt &symbol,
  const exprt &op,
  transt &trans)
{
  construct=constructt::OTHER;

  const irep_idt &instance=op.get(ID_instance);

  replace_mapt replace_map;

  std::list<irep_idt> new_symbols;

  forall_symbol_module_map(it, symbol_table.symbol_module_map, symbol.module)
  {
    const symbolt &symbol=lookup(it->second);
    
    if(symbol.type.id()!=ID_module)
    {
      // instantiate the symbol

      symbolt new_symbol(symbol);

      new_symbol.module=module;
      
      // Identifiers are Verilog::MODULE.id.id.id

      // strip old module      
      std::string identifier_without_module=
        std::string(id2string(symbol.name), symbol.module.size());

      std::string full_identifier;

      full_identifier=id2string(mode)+"::";
      full_identifier+=id2string(verilog_module_name(module));
      full_identifier+="."+id2string(instance);
      full_identifier+=identifier_without_module;

      new_symbol.pretty_name=strip_verilog_prefix(full_identifier);
      new_symbol.name=full_identifier;

      if(symbol_table.add(new_symbol))
      {
        error() << "name collision during module instantiation: "
                << new_symbol.name << eom;
        throw 0;
      }

      new_symbols.push_back(new_symbol.name);

      // build replace map

      std::pair<irep_idt, exprt> replace_pair;
      replace_pair.first=symbol.name;
      replace_pair.second=symbol_expr(new_symbol, CURRENT);
      replace_map.insert(replace_pair);
    }
  }

  // replace identifiers in macros

  for(const auto & it : new_symbols)
  {
    symbolt &symbol=symbol_table_lookup(it);
    replace_symbols(replace_map, symbol.value);
  }

  // do the trans

  {
    exprt tmp=symbol.value;

    if(tmp.id()!=ID_trans || tmp.operands().size()!=3)
    {
      error().source_location=op.source_location();
      error() << "Expected transition system, but got `"
              << tmp.id() << '\'' << eom;
      throw 0;
    }

    replace_symbols(replace_map, tmp);

    for(unsigned i=0; i<3; i++)
      trans.operands()[i].move_to_operands(tmp.operands()[i]);
  }

  instantiate_ports(instance, op, symbol, replace_map, trans);
}

/*******************************************************************\

Function: verilog_synthesist::synth_always

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_always(
  const verilog_alwayst &module_item)
{
  if(module_item.operands().size()!=1)
  {
    error().source_location=module_item.source_location();
    error() << "always module item expected to have one operand" << eom;
    throw 0;
  }

  construct=constructt::ALWAYS;
  event_guard=event_guardt::NONE;

  value_mapt always_value_map;
  value_map=&always_value_map;

  synth_statement(module_item.statement());

  for(const auto & it : value_map->final.changed)
  {
    assignmentt &assignment=assignments[it];
    assignment.next.value=value_map->final.symbol_map[it];
    assignment.next.move_assignments();
  }

  value_map=NULL;
}

/*******************************************************************\

Function: verilog_synthesist::synth_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_initial(
  const verilog_initialt &module_item)
{
  if(module_item.operands().size()!=1)
  {
    error().source_location=module_item.source_location();
    error() << "initial module item expected to have one operand" << eom;
    throw 0;
  }

  construct=constructt::INITIAL;
  event_guard=event_guardt::NONE;

  value_mapt initial_value_map;
  value_map=&initial_value_map;

  synth_statement(module_item.statement());
  
  for(const auto & it : value_map->final.changed)
  {
    assignmentt &assignment=assignments[it];
    assignment.init.value=value_map->final.symbol_map[it];
    assignment.init.move_assignments();    
  }

  value_map=NULL;
}

/*******************************************************************\

Function: verilog_synthesist::synth_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_decl(
  const verilog_declt &statement,
  transt &trans)
{
  forall_operands(it, statement)
  {
    if(it->id()==ID_equal)
    {
      // These are only allowed for module-level declarations,
      // not block-level.
      construct=constructt::INITIAL;
      event_guard=event_guardt::NONE;

      if(it->operands().size()!=2)
      {
        error() << "expected two operands in assignment" << eom;
        throw 0;
      }

      exprt lhs=it->op0();
      exprt rhs=it->op1();

      if(lhs.id()!=ID_symbol)
      {
        error() << "expected symbol on left hand side of assignment"
                << " but got `" << to_string(lhs) << '\'' << eom;
        throw 0;
      }

      const symbolt &symbol=lookup(to_symbol_expr(lhs));
      assignmentt &assignment=assignments[symbol.name];

      if(symbol.is_state_var)
      {
        synth_expr(rhs, symbol_statet::CURRENT);

        if(assignment.type==event_guardt::NONE)
          assignment.type=event_guardt::CLOCK;
        else if(assignment.type!=event_guardt::CLOCK)
        {
          error().source_location=statement.source_location();
          error() << "variable is combinational" << eom;
          throw 0;
        }

        if(!assignment.init.value.is_nil())
        {
          error().source_location=statement.source_location();
          error() << "variable already has initial value" << eom;
          throw 0;
        }

        assignment.init.value=rhs;
        assignment.init.assigned_previous.push_back(membert());
      }
      else
      {
        synth_expr(lhs, symbol_statet::SYMBOL);
        synth_expr(rhs, symbol_statet::SYMBOL);

        if(assignment.type==event_guardt::NONE)
          assignment.type=event_guardt::COMBINATIONAL;
        else if(assignment.type!=event_guardt::COMBINATIONAL)
        {
          error().source_location=statement.source_location();
          error() << "variable is clocked" << eom;
          throw 0;
        }

        equal_exprt equality(lhs, rhs);
        trans.invar().move_to_operands(equality);
      }
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_block(const verilog_blockt &statement)
{
  forall_operands(it, statement)
    synth_statement(static_cast<const verilog_statementt &>(*it));
}

/*******************************************************************\

Function: verilog_synthesist::synth_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_continuous_assign(
  const verilog_continuous_assignt &module_item,
  transt &trans)
{
  construct=constructt::OTHER;

  forall_operands(it, module_item)
  {
    if(it->id()!=ID_equal || it->operands().size()!=2)
    {
      error().source_location=it->source_location();
      error() << "unexpected continuous assignment" << eom;
      throw 0;
    }

    exprt lhs=it->op0();
    exprt rhs=it->op1();
    
    synth_expr(lhs, symbol_statet::SYMBOL);
    synth_expr(rhs, symbol_statet::SYMBOL);

    synth_continuous_assign(lhs, rhs, trans);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_continuous_assign(
  exprt &lhs,
  exprt &rhs,
  transt &trans)
{
  if(lhs.id()==ID_concatenation)
  {
    // split it up
    unsigned offset=0;
    
    // do it from right to left
    
    for(exprt::operandst::reverse_iterator
        it=lhs.operands().rbegin();
        it!=lhs.operands().rend();
        it++)
    {
      constant_exprt offset_constant;
      offset_constant.type()=natural_typet();
      offset_constant.set(ID_value, offset);

      if(it->type().id()==ID_bool)
      {
        exprt bit_extract(ID_extractbit, it->type());
        bit_extract.copy_to_operands(rhs, offset_constant);
        offset++;

        synth_continuous_assign(*it, bit_extract, trans);
      }
      else if(it->type().id()==ID_signedbv ||
              it->type().id()==ID_unsignedbv)
      {
        unsigned width=get_width(it->type());
      
        constant_exprt offset_constant2;
        offset_constant2.type()=natural_typet();
        offset_constant2.set(ID_value, offset+width-1);

        exprt bit_extract(ID_extractbits, it->type());
        bit_extract.copy_to_operands(rhs, offset_constant, offset_constant2);
        
        synth_continuous_assign(*it, bit_extract, trans);
        
        offset+=width;
      }
      else
      {
        error().source_location=it->source_location();
        error() << "continuous assignment to type `"
                << to_string(it->type())
                << "' not supported" << eom;
      }
    }
    
    return;
  }

  // get symbol

  symbolt &symbol=assignment_symbol(lhs);

  assignmentt &assignment=assignments[symbol.name];

  if(assignment.type==event_guardt::NONE)
    assignment.type=event_guardt::COMBINATIONAL;
  else if(assignment.type!=event_guardt::COMBINATIONAL)
  {
    error().source_location=lhs.source_location();
    error() << "variable is clocked" << eom;
    throw 0;
  }

  equal_exprt equality(lhs, rhs);
  trans.invar().move_to_operands(equality);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assign(
  const exprt &statement,
  bool blocking)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assign statement expected to have two operands" << eom;
    throw 0;
  }

  if(construct!=constructt::ALWAYS &&
     construct!=constructt::INITIAL)
  {
    error().source_location=statement.source_location();
    error() << "unexpected assignment statement" << eom;
    throw 0;
  }
  
  const exprt &lhs=statement.op0();
  exprt rhs=statement.op1();

  synth_expr(rhs, symbol_statet::CURRENT);

  // elaborate now?
  if(lhs.type().id()==ID_integer)
  {
    mp_integer i;
    simplify(rhs, ns);

    if(to_integer(rhs, i))
    {
      error().source_location=rhs.source_location();
      error() << "synthesis expects constant on rhs" << eom;
      throw 0;
    }
    
    if(lhs.id()!=ID_symbol)
    {
      error().source_location=lhs.source_location();
      error() << "synthesis expects symbol on lhs" << eom;
      throw 0;
    }
    
    values[to_symbol_expr(lhs).get_identifier()]=i;
  }
  else
    assignment(lhs, rhs, blocking);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assert(
  const verilog_assertt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assert statement expected to have two operands" << eom;
    throw 0;
  }

  const irep_idt &identifier=statement.get(ID_identifier);
  symbolt &symbol=symbol_table_lookup(identifier);
  
  synth_expr(symbol.value, symbol_statet::CURRENT);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assert_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assert_module_item(
  const verilog_module_itemt &module_item)
{
  if(module_item.operands().size()!=2)
  {
    error().source_location=module_item.source_location();
    error() << "assert module_item expected to have two operands" << eom;
    throw 0;
  }

  const irep_idt &identifier=module_item.get(ID_identifier);
  symbolt &symbol=symbol_table_lookup(identifier);
  
  construct=constructt::OTHER;

  synth_expr(symbol.value, symbol_statet::SYMBOL);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assume(
  const verilog_assumet &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "assume statement expected to have two operands" << eom;
    throw 0;
  }
  
  exprt condition=statement.condition();

  construct=constructt::OTHER;

  synth_expr(condition, symbol_statet::CURRENT);

  // add it as an invariant
  invars.push_back(condition);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assume_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assume_module_item(
  const verilog_module_itemt &module_item)
{
  if(module_item.operands().size()!=2)
  {
    error().source_location=module_item.source_location();
    error() << "assume module item expected to have two operands" << eom;
    throw 0;
  }

  exprt condition=module_item.op0();
  synth_expr(condition, symbol_statet::SYMBOL);

  // add it as an invariant
  invars.push_back(condition);
}

/*******************************************************************\

Function: verilog_synthesist::case_comparison

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::case_comparison(
  const exprt &case_operand,
  const exprt &pattern)
{
  // we need to take case of ?, x, z in the pattern
  const typet &pattern_type=pattern.type();
  
  if(pattern_type.id()==ID_verilog_signedbv ||
     pattern_type.id()==ID_verilog_unsignedbv)
  {
    // try to simplify the pattern
    exprt tmp=pattern;
    
    simplify(tmp, ns);
    
    if(tmp.id()!=ID_constant)
    {
      warning().source_location=pattern.source_location();
      warning() << "unexpected case pattern: " << to_string(tmp) << eom;
    }
    else
    {
      exprt new_case_operand=case_operand;

      // the pattern has the max type
      unsignedbv_typet new_type;
      new_type.set_width(pattern.type().get_int(ID_width));
      new_case_operand.make_typecast(new_type);
    
      // we are using masking!
    
      std::string new_pattern_value=
        id2string(to_constant_expr(tmp).get_value());

      // ?zx -> 0
      for(unsigned i=0; i<new_pattern_value.size(); i++)
        if(new_pattern_value[i]=='?' ||
           new_pattern_value[i]=='z' ||
           new_pattern_value[i]=='x')
          new_pattern_value[i]='0';
    
      constant_exprt new_pattern(new_type);
      new_pattern.set_value(new_pattern_value);

      std::string new_mask_value=
        id2string(to_constant_expr(tmp).get_value());

      // ?zx -> 0, 0 -> 1
      for(unsigned i=0; i<new_mask_value.size(); i++)
        if(new_mask_value[i]=='?' ||
           new_mask_value[i]=='z' ||
           new_mask_value[i]=='x')
          new_mask_value[i]='0';
        else
          new_mask_value[i]='1';

      constant_exprt new_mask(new_type);
      new_mask.set_value(new_mask_value);
    
      exprt bitand_expr=bitand_exprt(new_case_operand, new_mask);
    
      return equal_exprt(bitand_expr, new_pattern);
    }
  }

  if(pattern.type()==case_operand.type())
    return equal_exprt(case_operand, pattern);

  // the pattern has the max type
  exprt tmp_case_operand=typecast_exprt(case_operand, pattern.type());
  return equal_exprt(tmp_case_operand, pattern);
}

/*******************************************************************\

Function: verilog_synthesist::synth_case_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::synth_case_values(
  const exprt &values,
  const exprt &case_operand)
{
  if(values.id()==ID_default)
    return true_exprt();

  exprt::operandst op;
  
  op.reserve(values.operands().size());

  forall_operands(it, values)
  {
    exprt pattern=*it;
    synth_expr(pattern, symbol_statet::CURRENT);
    op.push_back(case_comparison(case_operand, pattern));
  }

  return disjunction(op);
}

/*******************************************************************\

Function: verilog_synthesist::synth_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_case(
  const verilog_statementt &statement)
{
  if(statement.operands().size()<1)
  {
    error().source_location=statement.source_location();
    error() << "case statement expected to have at least one operand" << eom;
    throw 0;
  }

  exprt case_operand=statement.op0();

  // do the argument of the case
  synth_expr(case_operand, symbol_statet::CURRENT);
  
  // we convert the rest to if-then-else
  exprt start;
  exprt *last_if=&start;

  for(unsigned i=1; i<statement.operands().size(); i++)
  {
    const exprt &e=statement.operands()[i];

    if(e.id()!=ID_case_item)
    {
      error() << "expected case_item" << eom;
      throw 0;
    }

    if(e.operands().size()!=2)
    {
      error().source_location=e.source_location();
      error() << "case_item expected to have two operands" << eom;
      throw 0;
    }

    exprt if_statement(ID_if);
    if_statement.reserve_operands(3);
    if_statement.operands().resize(2);

    if_statement.op0()=synth_case_values(e.op0(), case_operand);

    if_statement.op1()=e.op1();

    last_if->move_to_operands(if_statement);
    last_if=&last_if->operands().back();
  }

  // synthesize the new if-then-else

  if(!start.operands().empty())
    synth_statement(static_cast<verilog_statementt &>(start.op0()));
}

/*******************************************************************\

Function: verilog_synthesist::synth_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_if(
  const verilog_ift &statement)
{
  if(statement.operands().size()!=2 &&
     statement.operands().size()!=3)
  {
    error().source_location=statement.source_location();
    error() << "if statement expected to have two or three operands" << eom;
    throw 0;
  }

  exprt if_operand=statement.condition();
  synth_expr(if_operand, symbol_statet::CURRENT);

  if(if_operand.is_true())
  {
    synth_statement(statement.true_case());
    return;
  }

  // save current value_map pointer
  value_mapt *old_map=value_map;

  // produce new value maps
  value_mapt true_map(*value_map), false_map(*value_map);
  true_map.clear_changed();
  false_map.clear_changed();

  // true case
  {
    value_map=&true_map;
    synth_statement(statement.true_case());
  }
  
  // false case
  if(statement.operands().size()==3)
  {
    value_map=&false_map;
    synth_statement(statement.false_case());
  }

  // restore and merge
  value_map=old_map;

  // merge current map
  merge(if_operand, true_map.current, false_map.current, false, value_map->current);
  
  // merge final map
  merge(if_operand, true_map.final, false_map.final, true, value_map->final);
}

/*******************************************************************\

Function: verilog_synthesist::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::merge(
  const exprt &guard,
  const value_mapt::mapt &true_map,
  const value_mapt::mapt &false_map,
  bool use_previous_assignments,
  value_mapt::mapt &dest)
{
  // get true_map.changed + false_map.changed

  std::set<irep_idt> changed;

  changed.insert(true_map.changed.begin(), true_map.changed.end());
  changed.insert(false_map.changed.begin(), false_map.changed.end());

  for(const auto & it : changed)
  {
    const symbolt &symbol=lookup(it);

    exprt true_value=current_value(true_map, symbol, use_previous_assignments);
    exprt false_value=current_value(false_map, symbol, use_previous_assignments);
    
    // this is a phi-node equivalent
    if_exprt value;
    value.type()=symbol.type;
    value.cond()=guard;
    value.true_case().swap(true_value);
    value.false_case().swap(false_value);
    
    dest.symbol_map[symbol.name].swap(value);
    dest.changed.insert(symbol.name);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_event_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_event_guard(
  const verilog_event_guardt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "event_guard expected to have two operands" << eom;
    throw 0;
  }

  if(event_guard!=event_guardt::NONE)
  {
    error().source_location=statement.source_location();
    error() << "event guard already specified" << eom;
    throw 0;
  }

  const exprt &event_guard_expr=statement.guard();

  bool edge=false;

  // these guards are ORed
  exprt::operandst guards; 

  forall_operands(it, event_guard_expr)
    if(it->id()==ID_posedge || it->id()==ID_negedge)
    {
      edge=true;

      if(it->operands().size()!=1)
      {
        error().source_location=it->source_location();
        error() << "pos/negedge expected to have one operand" << eom;
        throw 0;
      }

      if(it->op0().id()!=ID_symbol)
      {
        error().source_location=it->source_location();
        error() << "pos/negedge expected to have symbol as operand, "
                   "but got "+it->op0().pretty();
        throw 0;
      }

      if(it->op0().type().id()!=ID_bool)
      {
        error().source_location=it->source_location();
        error() << "pos/negedge expected to have Boolean as operand, "
                   "but got "+to_string(it->op0().type());
        throw 0;
      }

      irep_idt identifier="conf::clock_enable_mode";

      // check symbol_table for clock guard

      if(symbol_table.symbols.find(identifier)!=symbol_table.symbols.end())
      {
        // found! we make it a guard

        guards.push_back(it->op0());

        error() << "Notice: using clock guard " << identifier << eom;
      }
    }

  event_guard=edge?event_guardt::CLOCK:event_guardt::COMBINATIONAL;

  if(guards.empty())
    synth_statement(statement.body());
  else
  {
    // new guards!
    exprt guard_expr=disjunction(guards);

    value_mapt *old_map=value_map;
    value_mapt true_map(*value_map), false_map(*value_map);
    true_map.clear_changed();
    false_map.clear_changed();

    value_map=&true_map;
    synth_statement(statement.body());

    value_map=old_map;
    merge(guard_expr, true_map.current, false_map.current, false, value_map->current);
    merge(guard_expr, true_map.final, false_map.final, true, value_map->final);
  }

  event_guard=event_guardt::NONE;
}

/*******************************************************************\

Function: verilog_synthesist::synth_delay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_delay(
  const verilog_delayt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "delay expected to have two operands" << eom;
    throw 0;
  }

  synth_statement(statement.body());
}

/*******************************************************************\

Function: verilog_synthesist::synth_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_for(const verilog_fort &statement)
{
  if(statement.operands().size()!=4)
  {
    error().source_location=statement.source_location();
    error() << "for expected to have four operands" << eom;
    throw 0;
  }

  synth_statement(statement.initialization());

  while(true)
  {  
    exprt tmp_guard=statement.condition();
    tmp_guard.make_typecast(bool_typet());
    synth_expr(tmp_guard, symbol_statet::CURRENT);
    simplify(tmp_guard, ns);
 
    if(!tmp_guard.is_constant())
    {
      error().source_location=statement.op1().source_location();
      error() << "synthesis failed to evaluate loop guard: `"
              << expr2verilog(tmp_guard) << '\'' << eom;
      throw 0;
    }

    if(tmp_guard.is_false()) break;
    
    // copy the body
    verilog_statementt tmp_body=statement.body();
    synth_statement(tmp_body);

    verilog_statementt tmp_inc=statement.inc_statement();
    synth_statement(tmp_inc);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_prepostincdec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_prepostincdec(const verilog_statementt &statement)
{
  if(statement.operands().size()!=1)
  {
    error().source_location=statement.source_location();
    throw statement.id_string()+" expected to have one operand";
  }

  // stupid implementation
  exprt one=
    from_integer(1, statement.op0().type());
    
  bool increment=
    statement.id()==ID_preincrement ||
    statement.id()==ID_postincrement;
  
  verilog_blocking_assignt assignment;
  assignment.lhs()=statement.op0();
  
  if(increment)
    assignment.rhs()=plus_exprt(statement.op0(), one);
  else
    assignment.rhs()=minus_exprt(statement.op0(), one);
  
  assignment.add_source_location()=statement.source_location();
  synth_statement(assignment);  
}

/*******************************************************************\

Function: verilog_synthesist::synth_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_while(
  const verilog_whilet &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "while expected to have two operands" << eom;
    throw 0;
  }

  while(true)
  {  
    exprt tmp_guard=statement.condition();
    tmp_guard.make_typecast(bool_typet());
    synth_expr(tmp_guard, symbol_statet::CURRENT);
    simplify(tmp_guard, ns);
 
    if(!tmp_guard.is_constant())
    {
      error().source_location=statement.op1().source_location();
      error() << "synthesis failed to evaluate loop guard: `"
              << expr2verilog(tmp_guard) << '\'' << eom;
      throw 0;
    }

    if(tmp_guard.is_false()) break;

    // copy the body!    
    verilog_statementt tmp_body=statement.body();
    synth_statement(tmp_body);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_repeat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_repeat(
  const verilog_repeatt &statement)
{
  if(statement.operands().size()!=2)
  {
    error().source_location=statement.source_location();
    error() << "repeat expected to have two operands" << eom;
    throw 0;
  }

  error().source_location=statement.source_location();
  error() << "cannot synthesize `repeat'" << eom;
  throw 0;
}

/*******************************************************************\

Function: verilog_synthesist::synth_forever

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_forever(
  const verilog_forevert &statement)
{
  if(statement.operands().size()!=1)
  {
    error().source_location=statement.source_location();
    error() << "forever expected to have one operand" << eom;
    throw 0;
  }

  error().source_location=statement.source_location();
  error() << "cannot synthesize `forever'" << eom;
  throw 0;
}

/*******************************************************************\

Function: verilog_synthesist::synth_function_call_or_task_enable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_function_call_or_task_enable(
  const verilog_function_callt &statement)
{
  // this is essentially inlined
  const symbol_exprt &function=to_symbol_expr(statement.function());
  
  irep_idt identifier=function.get_identifier();
  
  // We ignore everyting that starts with a '$',
  // e.g., $display etc
    
  if(!identifier.empty() && identifier[0]=='$')       
  {
    // ignore
  }
  else
  {
    const symbolt &symbol=lookup(identifier);
    
    if(symbol.type.id()!=ID_code)
    {
      error().source_location=statement.source_location();
      error() << "expected function or task as first operand" << eom;
      throw 0;
    }
    
    const code_typet &code_type=to_code_type(symbol.type);

    const code_typet::parameterst &parameters=
      code_type.parameters();

    const exprt::operandst &actuals=
      statement.op1().operands();
      
    if(parameters.size()!=actuals.size())
    {
      error().source_location=statement.source_location();
      error() << "wrong number of arguments" << eom;
      throw 0;
    }
    
    // do assignments to input parameters
    for(unsigned i=0; i<parameters.size(); i++)
    {
      const symbolt &a_symbol=lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_input))
      {
        verilog_blocking_assignt assignment;
        assignment.lhs()=a_symbol.symbol_expr();
        assignment.rhs()=actuals[i];
        assignment.add_source_location()=statement.source_location();
        synth_statement(assignment);
      }
    }

    synth_statement(to_verilog_statement(symbol.value));

    // do assignments to output parameters
    for(unsigned i=0; i<parameters.size(); i++)
    {
      const symbolt &a_symbol=lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_output))
      {
        verilog_blocking_assignt assignment;
        assignment.lhs()=actuals[i];
        assignment.rhs()=a_symbol.symbol_expr();
        assignment.add_source_location()=statement.source_location();
        synth_statement(assignment);
      }
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_statement(
  const verilog_statementt &statement)
{
  if(statement.id()==ID_block)
    synth_block(to_verilog_block(statement));
  else if(statement.id()==ID_case ||
          statement.id()==ID_casex ||
          statement.id()==ID_casez)
    synth_case(statement);
  else if(statement.id()==ID_blocking_assign)
    synth_assign(statement, true);
  else if(statement.id()==ID_continuous_assign)
  {
    error().source_location=statement.source_location();
    error() << "synthesis of procedural continuous assignment not supported" << eom;
    throw 0;
  }
  else if(statement.id()==ID_assert)
    synth_assert(to_verilog_assert(statement));
  else if(statement.id()==ID_assume)
    synth_assume(to_verilog_assume(statement));
  else if(statement.id()==ID_non_blocking_assign)
    synth_assign(statement, false);
  else if(statement.id()==ID_if)
    synth_if(to_verilog_if(statement));
  else if(statement.id()==ID_event_guard)
    synth_event_guard(to_verilog_event_guard(statement));
  else if(statement.id()==ID_delay)
    synth_delay(to_verilog_delay(statement));
  else if(statement.id()==ID_for)
    synth_for(to_verilog_for(statement));
  else if(statement.id()==ID_while)
    synth_while(to_verilog_while(statement));
  else if(statement.id()==ID_repeat)
    synth_repeat(to_verilog_repeat(statement));
  else if(statement.id()==ID_forever)
    synth_forever(to_verilog_forever(statement));
  else if(statement.id()==ID_function_call)
    synth_function_call_or_task_enable(to_verilog_function_call(statement));
  else if(statement.id()==ID_preincrement ||
          statement.id()==ID_predecrement ||
          statement.id()==ID_postincrement ||
          statement.id()==ID_postdecrement)
    synth_prepostincdec(statement);
  else if(statement.id()==ID_decl)
  {
    transt tmp_trans;
    synth_decl(to_verilog_decl(statement), tmp_trans);
  }
  else if(statement.id()==ID_skip)
  {
    // do nothing
  }
  else
  {
    error().source_location=statement.source_location();
    error() << "unexpected statement during synthesis: "
            << statement.id() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_module_item(
  const verilog_module_itemt &module_item,
  transt &trans)
{
  if(module_item.id()==ID_specify)
  {
  }
  else if(module_item.id()==ID_decl)
    synth_decl(to_verilog_decl(module_item), trans);
  else if(module_item.id()==ID_parameter_decl ||
          module_item.id()==ID_local_parameter_decl)
  {
  }
  else if(module_item.id()==ID_always)
    synth_always(to_verilog_always(module_item));
  else if(module_item.id()==ID_initial)
    synth_initial(to_verilog_initial(module_item));
  else if(module_item.id()==ID_continuous_assign)
    synth_continuous_assign(to_verilog_continuous_assign(module_item), trans);
  else if(module_item.id()==ID_inst)
    synth_module_instance(to_verilog_inst(module_item), trans);
  else if(module_item.id()==ID_inst_builtin)
    synth_module_instance_builtin(to_verilog_inst_builtin(module_item), trans);
  else if(module_item.id()==ID_generate_block)
  {
    error().source_location=module_item.source_location();
    error() << "unexpected generate module item during synthesis" << eom;
    throw 0;
  }
  else if(module_item.id()==ID_assert)
    synth_assert_module_item(module_item);
  else if(module_item.id()==ID_assume)
    synth_assume_module_item(module_item);
  else if(module_item.id()==ID_task)
  {
    // ignore for now
  }
  else
  {
    error().source_location=module_item.source_location();
    error() << "unexpected module item during synthesis: "
            << module_item.id() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_synthesist::symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::symbol_expr(
  const symbolt &symbol,
  curr_or_nextt curr_or_next)
{
  exprt result=exprt(curr_or_next==NEXT?ID_next_symbol:ID_symbol, symbol.type);
  result.set(ID_identifier, symbol.name);
  return result;
}

/*******************************************************************\

Function: verilog_synthesist::synth_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assignments(
  const symbolt &symbol,
  curr_or_nextt curr_or_next,
  exprt &new_value,
  exprt &constraints)
{
  if(new_value.is_nil())
    new_value=symbol_expr(symbol, CURRENT);
  
  // see if wire is used to define itself
  if(!symbol.is_state_var)
    post_process_wire(symbol.name, new_value);

  equal_exprt equality_expr;

  equality_expr.lhs()=symbol_expr(symbol, curr_or_next);
  equality_expr.rhs().swap(new_value);

  constraints.move_to_operands(equality_expr);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assignments(transt &trans)
{
  for(const auto & it : local_symbols)
  {
    symbolt &symbol=symbol_table_lookup(it);
    
    if(symbol.is_state_var && !symbol.is_macro)
    {
      assignmentt &assignment=assignments[symbol.name];

      if(assignment.type==event_guardt::COMBINATIONAL)
      {
        warning() << "Making " << symbol.name << " a wire" << eom;
        symbol.is_state_var=false;
      }

      if(symbol.is_state_var)
      {
        // only state variables can be initialized

        if(!assignment.init.value.is_nil())
          synth_assignments(symbol, CURRENT,
                            assignment.init.value,
                            trans.op1());

        synth_assignments(symbol, NEXT,
                          assignment.next.value,
                          trans.op2());
      }
      else
      {
        synth_assignments(symbol, CURRENT,
                          assignment.next.value,
                          trans.invar());
      }
    }
  }
  
  for(const auto & it : new_wires)
  {
    symbolt &symbol=symbol_table_lookup(it);
    assignmentt &assignment=assignments[symbol.name];

    synth_assignments(symbol, CURRENT,
                      assignment.next.value,
                      trans.invar());
  }

  // post-process initial state predicate to get rid
  // of unnecessary nondet_symbols

  post_process_initial(trans.op1());
}

/*******************************************************************\

Function: verilog_synthesist::current_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::current_value(
  const value_mapt::mapt &map,
  const symbolt &symbol,
  bool use_previous_assignments)
{
  if(!symbol.is_state_var)
  {
    if(use_previous_assignments)
    {
      // see if we have a previous assignment
      const assignmentt &assignment=assignments[symbol.name];
      const exprt &value=
        (construct==constructt::INITIAL)?
          assignment.init.value:
          assignment.next.value;

      if(value.is_not_nil())
        return value; // done
    }

    return symbol_expr(symbol, CURRENT);
  }
  else // latch
  {
    value_mapt::mapt::symbol_mapt::const_iterator it=
      map.symbol_map.find(symbol.name);
      
    if(it!=map.symbol_map.end())
      return it->second; // found
    
    if(use_previous_assignments)
    {
      // see if we have a previous assignment
      const assignmentt &assignment=assignments[symbol.name];
      const exprt &value=
        (construct==constructt::INITIAL)?
          assignment.init.value:assignment.next.value;

      if(value.is_not_nil())
        return value; // done
    }

    if(construct==constructt::ALWAYS)
      return symbol_expr(symbol, CURRENT);
    else
    {
      // make it some non-deterministic value
      exprt result=exprt(ID_nondet_symbol, symbol.type);
      result.set(ID_identifier, symbol.name);
      result.set("initial_value", true);
      return result;
    }
  }
}

/*******************************************************************\

Function: subexpressions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void subexpressions(const exprt &expr, std::multiset<exprt> &counters)
{
  counters.insert(expr);

  forall_operands(it, expr)
    subexpressions(*it, counters);
}

/*******************************************************************\

Function: verilog_synthesist::post_process_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::post_process_initial(exprt &constraints)
{
  // look for unused non-determinism constraints
  
  std::multiset<exprt> counters;

  forall_operands(it, constraints)
    subexpressions(*it, counters);

  Forall_operands(it, constraints)
  {
    if(it->id()==ID_equal && it->operands().size()==2)
    {
      exprt &lhs=it->op0(),
            &rhs=it->op1();

      #if 0
      if(lhs.id()==ID_symbol && 
         rhs.id()==ID_nondet_symbol &&
         lhs.get(ID_identifier)==rhs.get(ID_identifier))
      #else
      if(lhs.id()==ID_symbol && 
         rhs.id()==ID_nondet_symbol)
      #endif
      {
        if(counters.count(rhs)==1)
        {
          // not used elsewhere
          it->make_true();
        }
      }
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::post_process_wire

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::post_process_wire(
  const irep_idt &identifier,
  exprt &expr)
{
  // look if wire is used to define wire itself

  Forall_operands(it, expr)
    post_process_wire(identifier, *it);

  if(expr.id()==ID_symbol && 
     expr.get(ID_identifier)==identifier)
  {
    expr.id(ID_nondet_symbol);
  }
}

/*******************************************************************\

Function: verilog_synthesist::convert_module_items

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::convert_module_items(symbolt &symbol)
{
  assert(symbol.value.id()==ID_verilog_module);

  // clean up
  assignments.clear();
  invars.clear();

  // find out about symbols of this module

  forall_symbol_module_map(it, symbol_table.symbol_module_map, module)
    local_symbols.insert(it->second);

  // now convert the module items
  
  transt trans;

  for(const auto & it : symbol.value.operands())
  {
    const auto & module_item=static_cast<const verilog_module_itemt &>(it);
    synth_module_item(module_item, trans);
  }

  synth_assignments(trans);
  
  for(const auto & it : invars)
    trans.invar().copy_to_operands(it);

  trans.invar()=conjunction(trans.invar().operands());
  trans.init()=conjunction(trans.init().operands());
  trans.trans()=conjunction(trans.trans().operands());
  
  #if 0
  // debug
  forall_operands(it, trans.invar())
  {
    error() << "INVAR: " << to_string(*it) << eom;
    warning();
  }

  forall_operands(it, trans.init())
  {
    error() << "INIT: " << to_string(*it) << eom;
    warning();
  }

  forall_operands(it, trans.trans())
  {
    error() << "TRANS: " << to_string(*it) << eom;
    warning();
  }
  #endif

  symbol.value=trans;
}

/*******************************************************************\

Function: verilog_synthesist::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::typecheck()
{
  symbolt &symbol=symbol_table_lookup(module);
  if(symbol.value.id()==ID_trans) return; // done already
  convert_module_items(symbol);
}

/*******************************************************************\

Function: verilog_synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_synthesis(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler,
  const optionst &options)
{
  verilog_synthesist verilog_synthesis(
    symbol_table, module, options, message_handler);
  return verilog_synthesis.typecheck_main();
}
