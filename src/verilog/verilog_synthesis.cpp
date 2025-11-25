/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_synthesis.h"
#include "verilog_synthesis_class.h"

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/identifier.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "aval_bval_encoding.h"
#include "expr2verilog.h"
#include "sva_expr.h"
#include "verilog_expr.h"
#include "verilog_initializer.h"
#include "verilog_lowering.h"
#include "verilog_typecheck_expr.h"

#include <cassert>
#include <map>
#include <set>

/*******************************************************************\

Function: verilog_synthesist::synth_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::synth_expr(exprt expr, symbol_statet symbol_state)
{
  // First lower any Verilog-specific expressions
  auto lowered = verilog_lowering(expr);

  // Now replace symbols by known values, and expand
  // function definitions.
  return synth_expr_rec(lowered, symbol_state);
}

/*******************************************************************\

Function: verilog_synthesist::synth_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::synth_expr_rec(exprt expr, symbol_statet symbol_state)
{
  if(expr.id() == ID_function_call)
  {
    return expand_function_call(to_function_call_expr(expr), symbol_state);
  }
  else if(expr.id() == ID_sva_sequence_property_instance)
  {
    auto &instance = to_sva_sequence_property_instance_expr(expr);
    const symbolt &symbol = ns.lookup(instance.symbol());
    return synth_expr(symbol.value, symbol_state);
  }
  else if(expr.id() == ID_hierarchical_identifier)
  {
    expand_hierarchical_identifier(
      to_hierarchical_identifier_expr(expr), symbol_state);
    return expr;
  }

  // Do the operands recursively
  for(auto &op : expr.operands())
    op = synth_expr_rec(op, symbol_state);

  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=ns.lookup(to_symbol_expr(expr));

    if(symbol.is_macro)
    {
      // substitute
      assert(symbol.value.is_not_nil());

      // These aren't lowered yet
      auto lowered = verilog_lowering(symbol.value);

      // recursive call
      return synth_expr_rec(lowered, symbol_state);
    }
    else
    {
      switch(symbol_state)
      {
      case symbol_statet::SYMBOL:
        return expr; // leave as is

      case symbol_statet::CURRENT:
        return current_value(symbol);

      case symbol_statet::FINAL:
        return final_value(symbol);

      case symbol_statet::NONE:
        throw errort().with_location(expr.source_location())
          << "symbols not allowed here";
      }

      UNREACHABLE;
    }
  }
  else if(expr.id() == ID_typecast)
  {
    // We do some simplification
    if(to_typecast_expr(expr).op().type().id() == ID_integer)
      expr = simplify_expr(expr, ns);
    return expr;
  }
  else
    return expr; // leave as is

  UNREACHABLE;
}

// 1800-2017 16.12.2 Sequence property
// Sequences are by default _weak_ when used in assert property
// or assume property, and are _strong_ when used in cover property.
// This flips when below the SVA not operator.
void verilog_synthesist::set_default_sequence_semantics(
  exprt &expr,
  sva_sequence_semanticst semantics)
{
  if(expr.id() == ID_sva_sequence_property)
  {
    // apply
    if(semantics == sva_sequence_semanticst::WEAK)
      expr.id(ID_sva_implicit_weak);
    else
      expr.id(ID_sva_implicit_strong);
  }
  else if(expr.id() == ID_sva_not)
  {
    // flip
    semantics = semantics == sva_sequence_semanticst::WEAK
                  ? sva_sequence_semanticst::STRONG
                  : sva_sequence_semanticst::WEAK;

    set_default_sequence_semantics(to_sva_not_expr(expr).op(), semantics);
  }
  else
  {
    for(auto &op : expr.operands())
      set_default_sequence_semantics(op, semantics);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synthesis_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<mp_integer>
verilog_synthesist::synthesis_constant(const exprt &expr)
{
  exprt synthesised = synth_expr(expr, symbol_statet::CURRENT);

  exprt simplified = simplify_expr(synthesised, ns);

  if(!simplified.is_constant())
    return {};

  if(simplified.type().id() == ID_bool)
    return simplified.is_true() ? 1 : 0;

  auto number = numeric_cast<mp_integer>(to_constant_expr(simplified));
  if(!number.has_value())
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      false,
      "synthesis_constant expects a numerical type",
      simplified.pretty());

  return number.value();
}

/*******************************************************************\

Function: verilog_synthesist::synth_lhs_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::synth_lhs_expr(exprt expr)
{
  // case-split on possible expressions on the LHS of an assignment
  if(expr.id() == ID_symbol)
  {
    return expr; // leave as is
  }
  else if(expr.id() == ID_concatenation)
  {
    for(auto &op : expr.operands())
      op = synth_lhs_expr(op);

    return expr;
  }
  else if(expr.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(expr);
    part_select.src() = synth_lhs_expr(part_select.src());
    // The indices are expected to be constants.
    return expr;
  }
  else if(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(expr);
    part_select.src() = synth_lhs_expr(part_select.src());
    // The index need not be a constant, and is _not_ an lhs.
    part_select.index() =
      synth_expr(part_select.index(), symbol_statet::CURRENT);
    return expr;
  }
  else if(expr.id() == ID_index)
  {
    auto &index_expr = to_index_expr(expr);
    // The array is an 'lhs' but the index is not.
    index_expr.array() = synth_lhs_expr(index_expr.array());
    index_expr.index() = synth_expr(index_expr.index(), symbol_statet::CURRENT);
    return expr;
  }
  else if(expr.id() == ID_extractbit)
  {
    auto &extractbit_expr = to_extractbit_expr(expr);
    // The vector is an 'lhs' but the bit index is not.
    extractbit_expr.src() = synth_lhs_expr(extractbit_expr.src());
    extractbit_expr.index() =
      synth_expr(extractbit_expr.index(), symbol_statet::CURRENT);
    return expr;
  }
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    member_expr.struct_op() = synth_lhs_expr(member_expr.struct_op());
    return expr;
  }
  else
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      false, "unexpected lhs during synthesis", expr.pretty());
  }
}

/*******************************************************************\

Function: verilog_synthesist::value_mapt::guarded_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::value_mapt::guarded_expr(exprt expr) const
{
  if(guard.empty())
    return expr;
  else
    return implies_exprt{conjunction(guard), std::move(expr)};
}

/*******************************************************************\

Function: verilog_synthesist::function_locality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::function_locality(const symbolt &function_symbol)
{
  // Find all local symbols of the function, mark their
  // assignments as local.
  auto prefix = id2string(function_symbol.name) + '.';
  for(auto &symbol : symbol_table.symbols)
  {
    if(symbol.first.starts_with(prefix))
    {
      assignments[symbol.first].is_cycle_local = true;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::expand_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::expand_function_call(
  const function_call_exprt &call,
  symbol_statet symbol_state)
{
  // Is it a 'system function call'?
  if(call.is_system_function_call())
  {
    auto identifier = to_symbol_expr(call.function()).get_identifier();
    if(identifier == "$ND")
    {
      std::string identifier =
        id2string(module) + "::nondet::" + std::to_string(nondet_count++);

      auto arguments = call.arguments();
      exprt select_one(
        ID_constraint_select_one, call.type(), std::move(arguments));
      select_one.set(ID_identifier, identifier);
      return select_one.with_source_location(call);
    }
    else if(identifier == "$past")
    {
      auto what = call.arguments()[0];
      auto ticks = call.arguments().size() < 2
                     ? from_integer(1, integer_typet())
                     : call.arguments()[1];
      return verilog_past_exprt{what, ticks}.with_source_location(call);
    }
    else if(
      identifier == "$stable" || identifier == "$rose" ||
      identifier == "$fell" || identifier == "$changed")
    {
      DATA_INVARIANT(call.arguments().size() >= 1, "must have argument");
      auto what = call.arguments()[0];
      auto past = verilog_past_exprt{what, from_integer(1, integer_typet())}
                    .with_source_location(call);

      auto lsb = [](exprt expr) {
        return extractbit_exprt{
          std::move(expr), from_integer(0, integer_typet{})};
      };

      if(identifier == "$stable")
        return equal_exprt{what, past};
      else if(identifier == "$changed")
        return notequal_exprt{what, past};
      else if(identifier == "$rose")
        return and_exprt{not_exprt{lsb(past)}, lsb(what)};
      else if(identifier == "$fell")
        return and_exprt{lsb(past), not_exprt{lsb(what)}};
      else
        DATA_INVARIANT(false, "all cases covered");
    }
    else if(identifier == "$countones")
    {
      // lower to popcount
      DATA_INVARIANT(
        call.arguments().size() == 1, "$countones must have one argument");
      auto what = synth_expr(call.arguments()[0], symbol_state); // rec. call
      return popcount_exprt{what, call.type()};
    }
    else
    {
      // Attempt to constant fold.
      verilog_typecheck_exprt verilog_typecheck_expr(
        standard, false, ns, get_message_handler());
      auto result =
        verilog_typecheck_expr.elaborate_constant_system_function_call(call);
      if(!result.is_constant())
      {
        throw errort().with_location(call.source_location())
          << "cannot synthesise system function " << to_string(call.function());
      }

      return result;
    }
  }

  // check some restrictions
  if(construct == constructt::OTHER)
  {
    throw errort().with_location(call.source_location())
      << "function call not allowed here";
  }

  // this is essentially inlined
  const symbol_exprt &function=to_symbol_expr(call.function());

  const symbolt &symbol=ns.lookup(function);
  
  if(symbol.type.id()!=ID_code)
  {
    throw errort().with_location(call.source_location())
      << "function call expects function argument";
  }
  
  const code_typet &code_type=to_code_type(symbol.type);

  if(code_type.return_type()==empty_typet())
  {
    throw errort().with_location(call.source_location())
      << "function call cannot call task";
  }
  
  const code_typet::parameterst &parameters=
    code_type.parameters();
    
  const exprt::operandst &actuals=
    call.op1().operands();
    
  if(parameters.size()!=actuals.size())
  {
    throw errort().with_location(call.source_location())
      << "wrong number of arguments";
  }

  // preserve locality of function-local variables
  function_locality(symbol);

  // do assignments to function parameters
  for(unsigned i=0; i<parameters.size(); i++)
  {
    const symbolt &a_symbol=ns.lookup(parameters[i].get_identifier());
    verilog_blocking_assignt assignment{
      a_symbol.symbol_expr().with_source_location(call), actuals[i]};
    assignment.add_source_location()=call.source_location();
    synth_statement(assignment);
  }

  synth_statement(to_verilog_statement(symbol.value));

  // replace function call by return value symbol
  const symbolt &return_symbol=
    ns.lookup(id2string(symbol.name)+"."+
              id2string(symbol.base_name));

  // get the current value
  auto result = synth_expr(return_symbol.symbol_expr(), symbol_statet::CURRENT);

  return result;
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
  expr.lhs() = synth_expr(expr.lhs(), symbol_state);

  if(expr.lhs().id() != ID_symbol)
  {
    throw errort().with_location(expr.source_location())
      << "synthesis expected symbol on lhs of `.'";
  }

  if(expr.lhs().type().id() != ID_module_instance)
  {
    throw errort().with_location(expr.source_location())
      << "synthesis expected module instance on lhs of `.', but got `"
      << to_string(expr.lhs().type()) << '\'';
  }

  const irep_idt &lhs_identifier = expr.lhs().get(ID_identifier);

  // rhs
  const irep_idt &rhs_identifier = expr.rhs().get_identifier();

  // just patch together

  irep_idt full_identifier =
    id2string(lhs_identifier) + '.' + id2string(rhs_identifier);

  // Note: the instance copy may not yet be in symbol table,
  // as the inst module item may be later.
  // The type checker already checked that it's fine.

  symbol_exprt new_symbol{full_identifier, expr.type()};
  new_symbol.add_source_location()=expr.source_location();
  expr.swap(new_symbol);
}

/*******************************************************************\

Function: verilog_synthesist::assignment_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::assignment_rec(
  const exprt &lhs,
  const exprt &rhs,
  bool blocking)
{
  if(lhs.id()==ID_concatenation) // split it up                                
  {
    // TODO: split it up more intelligently;
    // bit-wise is wasteful.
    mp_integer offset = 0;

    // do it from right to left
    
    for(exprt::operandst::const_reverse_iterator
        it=lhs.operands().rbegin();
        it!=lhs.operands().rend();
        it++)
    {
      auto offset_constant = from_integer(offset, natural_typet{});

      if(it->type().id()==ID_bool)
      {
        exprt bit_extract = extractbit_exprt{rhs, offset_constant};
        ++offset;

        assignment_rec(*it, bit_extract, blocking);
      }
      else if(it->type().id()==ID_signedbv ||
              it->type().id()==ID_unsignedbv)
      {
        extractbits_exprt bit_extract(rhs, offset_constant, it->type());

        assignment_rec(*it, bit_extract, blocking);

        auto width = get_width(it->type());
        offset+=width;
      }
      else
      {
        throw errort().with_location(it->source_location())
          << "assignment to type `" << to_string(it->type())
          << "' not supported";
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
    throw errort().with_location(lhs.source_location())
      << "assignment to non-register";
  }

  if(construct==constructt::ALWAYS &&
     event_guard==event_guardt::NONE)
  {
    throw errort().with_location(lhs.source_location())
      << "assignment in 'always' context without event guard";
  }

  if(construct == constructt::ALWAYS_FF && event_guard == event_guardt::NONE)
  {
    throw errort().with_location(lhs.source_location())
      << "assignment in 'always_ff' context without event guard";
  }

  {
    event_guardt new_type;

    if(construct == constructt::INITIAL)
      new_type=event_guardt::CLOCK;
    else if(construct == constructt::ALWAYS_COMB)
      new_type = event_guardt::COMBINATIONAL;
    else
      new_type = event_guard;

    assignmentt &assignment=assignments[symbol.name];

    if(assignment.is_cycle_local)
    {
    }
    else
    {
      if(assignment.type == event_guardt::NONE)
        assignment.type = new_type;
      else if(assignment.type != new_type)
      {
        throw errort().with_location(lhs.source_location())
          << "conflicting assignment types for `" << symbol.base_name
          << "' (new: " << as_string(new_type)
          << ", old: " << as_string(assignment.type) << ")";
      }

      membert member;
      assignment_member_rec(
        lhs,
        member,
        (construct == constructt::INITIAL) ? assignment.init : assignment.next);
    }
  }

  {
    assert(value_map!=NULL);

    auto new_value = assignment_rec(lhs, rhs); // start of recursion

    if(new_value.is_not_nil())
    {
      // These can explode if the symbol is assigned more than once
      // and also used more than once, e.g., in a multi-dimensional array.
      // We add a fresh symbol for anything that is not trivial
      // to prevent that.
      if(new_value.id() != ID_symbol && new_value.id() != ID_constant)
      {
        replace_by_wire(new_value, symbol);
      }

      if(blocking)
        value_map->current.assign(symbol.name, new_value);

      value_map->final.assign(symbol.name, new_value);
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::assignment_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::assignment_rec(const exprt &lhs, const exprt &rhs)
{
  if(lhs.id()==ID_symbol)
  {
    return rhs;
  }
  else if(lhs.id()==ID_index ||
          lhs.id()==ID_extractbit)
  {
    if(lhs.operands().size()!=2)
    {
      throw errort() << "index takes two operands";
    }

    const exprt &lhs_array = to_binary_expr(lhs).op0();
    const exprt &lhs_index = to_binary_expr(lhs).op1();

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    with_exprt new_rhs(lhs_array, lhs_index, rhs);

    // do the array
    new_rhs.old() = synth_expr(new_rhs.old(), symbol_statet::FINAL);

    // do the index
    new_rhs.where() = synth_expr(new_rhs.where(), symbol_statet::CURRENT);

    // do the value
    return assignment_rec(lhs_array, new_rhs); // recursive call
  }
  else if(lhs.id() == ID_verilog_non_indexed_part_select)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_non_indexed_part_select_expr(lhs);

    const exprt &lhs_src = part_select.src();
    const exprt &lhs_msb = part_select.msb();
    const exprt &lhs_lsb = part_select.lsb();

    mp_integer from, to;

    if(to_integer_non_constant(lhs_msb, to))
    {
      throw errort().with_location(lhs_msb.source_location())
        << "failed to convert range";
    }

    if(to_integer_non_constant(lhs_lsb, from))
    {
      throw errort().with_location(lhs_lsb.source_location())
        << "failed to convert range";
    }

    if(from > to)
      std::swap(from, to);

    // redundant?
    if(from == 0 && to == get_width(lhs_src.type()) - 1)
    {
      return assignment_rec(lhs_src, rhs); // recursive call
    }

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    exprt synth_lhs_src(lhs_src);

    // do the array, but just once
    synth_lhs_src = synth_expr(synth_lhs_src, symbol_statet::FINAL);

    exprt last_value;
    last_value.make_nil();

    const auto rhs_width = get_width(lhs_src.type());

    // We drop bits that are out of bounds
    auto from_in_range = std::max(mp_integer{0}, from);
    auto to_in_range = std::min(rhs_width - 1, to);

    // now add the indexes in the range
    for(mp_integer i = from_in_range; i <= to_in_range; ++i)
    {
      exprt offset = from_integer(i - from, integer_typet());

      exprt rhs_extractbit = extractbit_exprt{rhs, std::move(offset)};

      exprt count = from_integer(i, integer_typet());

      exprt new_rhs =
        with_exprt{synth_lhs_src, std::move(count), std::move(rhs_extractbit)};

      // do the value
      exprt new_value = assignment_rec(lhs_src, new_rhs); // recursive call

      if(last_value.is_not_nil())
      {
        // chain the withs
        to_with_expr(new_value).old() = std::move(last_value);
      }

      last_value = std::move(new_value);
    }

    return last_value;
  }
  else if(
    lhs.id() == ID_verilog_indexed_part_select_plus ||
    lhs.id() == ID_verilog_indexed_part_select_minus)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(lhs);

    const exprt &lhs_src = part_select.src();
    const exprt &lhs_index = part_select.index();
    const exprt &lhs_width = part_select.width();

    auto index_opt = synthesis_constant(lhs_index);

    if(!index_opt.has_value())
    {
      throw errort().with_location(lhs_index.source_location())
        << "failed to convert part select index";
    }

    auto width_opt = synthesis_constant(lhs_width);

    if(!width_opt.has_value())
    {
      throw errort().with_location(lhs_width.source_location())
        << "failed to convert part select width";
    }

    mp_integer index = *index_opt, width = *width_opt;

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    exprt synth_lhs_src(lhs_src);

    // do the array, but just once
    synth_lhs_src = synth_expr(synth_lhs_src, symbol_statet::FINAL);

    exprt last_value;
    last_value.make_nil();

    const auto rhs_width = get_width(lhs_src.type());

    // We drop bits that are out of bounds
    auto from_in_range = std::max(mp_integer{0}, index);
    auto to_in_range = std::min(rhs_width - 1, index + width - 1);

    // now add the indexes in the range
    for(mp_integer i = from_in_range; i <= to_in_range; ++i)
    {
      exprt offset = from_integer(i - index, integer_typet());

      exprt rhs_extractbit = extractbit_exprt{rhs, std::move(offset)};

      exprt count = from_integer(i, integer_typet());

      exprt new_rhs =
        with_exprt{synth_lhs_src, std::move(count), std::move(rhs_extractbit)};

      // do the value
      exprt new_value = assignment_rec(lhs_src, new_rhs); // recursive call

      if(last_value.is_not_nil())
      {
        // chain the withs
        to_with_expr(new_value).old() = std::move(last_value);
      }

      last_value = std::move(new_value);
    }

    return last_value;
  }
  else if(lhs.id() == ID_member)
  {
    const auto &member_expr = to_member_expr(lhs);
    const exprt &lhs_compound = member_expr.struct_op();
    auto component_name = member_expr.get_component_name();

    if(
      lhs_compound.type().id() == ID_struct ||
      lhs_compound.type().id() == ID_union)
    {
      // turn
      //   s.m=e
      // into
      //   s'==s WITH [m:=e]
      auto synth_compound = synth_expr(lhs_compound, symbol_statet::FINAL);

      with_exprt new_rhs{
        synth_compound, member_designatort{component_name}, rhs};

      // recursive call
      return assignment_rec(lhs_compound, new_rhs); // recursive call
    }
    else
    {
      throw errort() << "unexpected member lhs: " << lhs_compound.type().id();
    }
  }
  else
  {
    throw errort() << "unexpected lhs: " << lhs.id();
  }
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
  PRECONDITION(what.is_not_nil());

  symbolt new_symbol;
  
  do
  {
    unsigned c=temporary_counter++;
    new_symbol.name=id2string(base.name)+"_aux"+std::to_string(c);
    new_symbol.base_name=id2string(base.base_name)+"_aux"+std::to_string(c);
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
  
  if(symbol_table.add(new_symbol))
  {
    throw errort() << "failed to add replace_by_wire symbol";
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
      throw errort() << "index takes two operands";
    }

    exprt tmp_lhs_op1 = simplify_expr(to_binary_expr(lhs).op1(), ns);

    // constant index?
    mp_integer index;
    if(to_integer_non_constant(tmp_lhs_op1, index))
    {
      // done
      add_assignment_member(lhs, member, data);
    }
    else
    {
      // do the value
      member.push_back(index);
      assignment_member_rec(to_binary_expr(lhs).op0(), member, data);
      member.pop_back();
    }
  }
  else if(lhs.id() == ID_verilog_non_indexed_part_select)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_non_indexed_part_select_expr(lhs);

    const exprt &lhs_bv = part_select.src();
    const exprt &lhs_index_one = part_select.msb();
    const exprt &lhs_index_two = part_select.lsb();

    mp_integer from, to;

    if(to_integer_non_constant(lhs_index_one, from))
    {
      throw errort().with_location(lhs_index_one.source_location())
        << "failed to convert range";
    }

    if(to_integer_non_constant(lhs_index_two, to))
    {
      throw errort().with_location(lhs_index_two.source_location())
        << "failed to convert range";
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
  else if(
    lhs.id() == ID_verilog_indexed_part_select_plus ||
    lhs.id() == ID_verilog_indexed_part_select_minus)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(lhs);

    const exprt &lhs_bv = part_select.src();
    const exprt &lhs_index = part_select.index();
    const exprt &lhs_width = part_select.width();

    auto index_opt = synthesis_constant(lhs_index);

    if(!index_opt.has_value())
    {
      throw errort().with_location(lhs_index.source_location())
        << "failed to convert part select index";
    }

    mp_integer index = index_opt.value(), width;

    if(to_integer_non_constant(lhs_width, width))
    {
      throw errort().with_location(lhs_width.source_location())
        << "failed to convert part select width";
    }

    member.push_back(mp_integer());

    // now add the indexes in the range
    for(mp_integer i = index; i <= index + width - 1; ++i)
    {
      // do the value
      member.back() = i;
      assignment_member_rec(lhs_bv, member, data);
    }

    member.pop_back();
  }
  else if(lhs.id() == ID_member)
  {
    add_assignment_member(lhs, member, data);
  }
  else
  {
    throw errort() << "unexpected lhs: " << lhs.id();
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
      throw errort().with_location(lhs.source_location())
        << "conflict with previous assignment";
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

const symbolt &verilog_synthesist::assignment_symbol(const exprt &lhs)
{
  const exprt *e=&lhs;

  while(1)
  {
    if(e->id()==ID_index)
    {
      if(e->operands().size()!=2)
      {
        throw errort() << "index takes two operands";
      }

      e = &to_index_expr(*e).op0();

      if(e->type().id()!=ID_array)
      {
        throw errort() << "index expects array operand";
      }
    }
    else if(e->id()==ID_extractbit)
    {
      if(e->operands().size()!=2)
      {
        throw errort() << "extractbit takes two operands";
      }

      e = &to_extractbit_expr(*e).src();
    }
    else if(e->id() == ID_verilog_non_indexed_part_select)
    {
      e = &to_verilog_non_indexed_part_select_expr(*e).src();
    }
    else if(
      e->id() == ID_verilog_indexed_part_select_plus ||
      e->id() == ID_verilog_indexed_part_select_minus)
    {
      e = &to_verilog_indexed_part_select_plus_or_minus_expr(*e).src();
    }
    else if(e->id()==ID_symbol)
    {
      // get identifier

      const irep_idt &identifier=e->get(ID_identifier);

      symbol_table_baset::symbolst::const_iterator it =
        symbol_table.symbols.find(identifier);

      if(it==symbol_table.symbols.end())
      {
        throw errort() << "assignment failed to find symbol `" << identifier
                       << '\'';
      }

      return it->second;
    }
    else if(e->id() == ID_member)
    {
      e = &to_member_expr(*e).struct_op();
    }
    else
    {
      throw errort().with_location(e->source_location())
        << "synthesis: failed to get identifier";
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
  const module_typet::portt &port,
  const exprt &value,
  const replace_mapt &replace_map,
  const source_locationt &source_location,
  transt &trans)
{
  irep_idt port_identifier = port.identifier();

  replace_mapt::const_iterator it = replace_map.find(port_identifier);

  if(it==replace_map.end())
  {
    throw errort().with_location(source_location)
      << "failed to find port symbol " << port_identifier << " in replace_map";
  }

  // Much like
  //   always @(*) port = value for an input, and
  //   always @(*) value = port for an output.
  // Note that the types need not match.
  exprt lhs, rhs;

  if(port.output())
  {
    lhs = value;
    rhs = typecast_exprt::conditional_cast(it->second, value.type());
  }
  else
  {
    lhs = it->second;
    rhs = typecast_exprt::conditional_cast(value, it->second.type());
  }

  verilog_forcet assignment{lhs, rhs};

  assignment.add_source_location() = source_location;

  verilog_event_guardt event_guard;
  event_guard.add_source_location() = source_location;
  event_guard.body() = assignment;

  verilog_always_baset always(ID_verilog_always, event_guard, source_location);
  synth_always_base(always);
}

/*******************************************************************\

Function: verilog_synthesist::instantiate_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::instantiate_ports(
  const irep_idt &instance,
  const verilog_instt::instancet &inst,
  const symbolt &symbol,
  const replace_mapt &replace_map,
  transt &trans)
{
  if(inst.connections().empty())
    return;

  auto &module_type = to_module_type(symbol.type);

  // named port connection?

  if(inst.named_port_connections())
  {
    const auto &ports = module_type.ports();
    auto port_map = module_type.port_map();

    // no requirement that all ports are connected
    for(const auto &connection : inst.connections())
    {
      auto &named_connection = to_verilog_named_port_connection(connection);
      auto port_it =
        port_map.find(to_symbol_expr(named_connection.port()).get_identifier());
      CHECK_RETURN(port_it != port_map.end());
      auto &port = port_it->second;
      const exprt &value = named_connection.value();

      if(value.is_not_nil())
      {
        instantiate_port(
          port, value, replace_map, inst.source_location(), trans);
      }
    }

    std::set<irep_idt> connected_ports;

    for(const auto &connection : inst.connections())
    {
      auto &named_connection = to_verilog_named_port_connection(connection);
      connected_ports.insert(
        to_symbol_expr(named_connection.port()).get_identifier());
    }

    // unconnected inputs may be given a default value
    for(auto &port : ports)
      if(port.input())
      {
        auto identifier = port.identifier();
        if(connected_ports.find(identifier) == connected_ports.end())
        {
          auto &port_symbol = ns.lookup(identifier);
          if(port_symbol.value.is_not_nil())
            instantiate_port(
              port,
              port_symbol.value,
              replace_map,
              inst.source_location(),
              trans);
        }
      }
  }
  else // just a list without names
  {
    const auto &ports = module_type.ports();

    if(inst.connections().size() != ports.size())
    {
      throw errort().with_location(inst.source_location())
        << "wrong number of ports: expected " << ports.size() << " but got "
        << inst.connections().size();
    }

    auto p_it = ports.begin();

    for(const auto &connection : inst.connections())
    {
      DATA_INVARIANT(connection.is_not_nil(), "all ports must be connected");

      instantiate_port(
        *p_it, connection, replace_map, inst.source_location(), trans);

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
  const irep_idt &module_identifier = statement.get_module();

  // must be in symbol_table
  const symbolt &module_symbol = ns.lookup(module_identifier);

  // make sure the module is synthesized already
  verilog_synthesis(
    symbol_table,
    module_identifier,
    standard,
    ignore_initial,
    initial_zero,
    get_message_handler());

  for(auto &instance : statement.instances())
    expand_module_instance(module_symbol, instance, trans);
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

  for(auto &instance : module_item.instances())
  {
    // check built-in ones
    if(module==ID_bufif0 ||
       module==ID_bufif1 ||
       module==ID_notif0 ||
       module==ID_notif1)
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(module==ID_nmos ||
            module==ID_pmos ||
            module==ID_rnmos ||
            module==ID_rpmos)
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(
      module == ID_and || module == ID_nand || module == ID_or ||
      module == ID_nor || module == ID_xor || module == ID_xnor)
    {
      // 1800-2017 28.4 and, nand, nor, or, xor, and xnor gates
      DATA_INVARIANT(
        instance.connections().size() >= 2,
        "binary primitive gates should have at least two connections");

      // One output, one or more inputs.
      auto &connections = instance.connections();
      auto &output = connections[0];

      irep_idt id = instance.type().id() == ID_bool
                      ? module
                      : irep_idt{"bit" + id2string(module)};

      exprt::operandst operands;

      // iterate over the module inputs
      for(std::size_t i = 1; i < connections.size(); i++)
      {
        operands.push_back(connections[i]);
      }

      auto op = exprt{id, instance.type(), std::move(operands)};

      equal_exprt constraint{output, op};
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(module==ID_buf)
    {
      assert(instance.connections().size() >= 2);

      for(unsigned i = 0; i < instance.connections().size() - 1; i++)
      {
        equal_exprt constraint{
          instance.connections()[i], instance.connections().back()};

        assert(trans.operands().size()==3);
        trans.invar().add_to_operands(std::move(constraint));
      }
    }
    else if(module==ID_not)
    {
      assert(instance.connections().size() >= 2);

      // May have multiple outputs. The input is the last connection.
      auto &input = instance.connections().back();
      exprt rhs;

      if(input.type().id() == ID_bool)
        rhs = not_exprt{input};
      else
        rhs = bitnot_exprt{input};

      rhs.add_source_location() = module_item.source_location();

      for(std::size_t i = 0; i < instance.connections().size() - 1; i++)
      {
        auto &lhs = instance.connections()[i];
        auto constraint = equal_exprt{lhs, rhs};
        trans.invar().add_to_operands(std::move(constraint));
      }
    }
    else if(module=="tranif0" ||
            module=="tranif1" ||
            module=="rtranif1" ||
            module=="rtranif0")
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else if(module=="tran"  ||
            module=="rtran")
    {
      // add to general constraints

      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type()=bool_typet();
      constraint.set(ID_module, module);
    
      assert(trans.operands().size()==3);
      trans.invar().add_to_operands(std::move(constraint));
    }
    else
    {
      throw errort().with_location(module_item.source_location())
        << "do not know how to synthesize " << module;
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
  const symbolt &module_symbol,
  const verilog_instt::instancet &instance,
  transt &trans)
{
  construct=constructt::OTHER;

  replace_mapt replace_map;

  std::list<irep_idt> new_symbols;

  for(auto it =
        symbol_table.symbol_module_map.lower_bound(module_symbol.module);
      it != symbol_table.symbol_module_map.upper_bound(module_symbol.module);
      it++)
  {
    const symbolt &symbol=ns.lookup(it->second);
    
    if(symbol.type.id()!=ID_module)
    {
      // instantiate the symbol

      symbolt new_symbol(symbol);

      new_symbol.module=module;

      // Identifier Verilog::INSTANTIATED_MODULE.X
      // is turned into Verilog::MODULE.id.instance::X

      // strip old module      
      std::string identifier_without_module=
        std::string(id2string(symbol.name), symbol.module.size());

      std::string full_identifier =
        id2string(instance.identifier()) + identifier_without_module;

      new_symbol.pretty_name=strip_verilog_prefix(full_identifier);
      new_symbol.name=full_identifier;

      if(symbol_table.add(new_symbol))
      {
        throw errort() << "name collision during module instantiation: "
                       << new_symbol.name;
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
    exprt tmp = module_symbol.value;

    if(tmp.id()!=ID_trans || tmp.operands().size()!=3)
    {
      throw errort().with_location(instance.source_location())
        << "Expected transition system, but got `" << tmp.id() << '\'';
    }

    replace_symbols(replace_map, tmp);

    for(unsigned i=0; i<3; i++)
      trans.operands()[i].add_to_operands(std::move(tmp.operands()[i]));
  }

  instantiate_ports(
    instance.base_name(), instance, module_symbol, replace_map, trans);
}

/*******************************************************************\

Function: verilog_synthesist::synth_always_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_always_base(
  const verilog_always_baset &module_item)
{
  if(module_item.id() == ID_verilog_always)
    construct = constructt::ALWAYS;
  else if(module_item.id() == ID_verilog_always_comb)
    construct = constructt::ALWAYS_COMB;
  else if(module_item.id() == ID_verilog_always_ff)
    construct = constructt::ALWAYS_FF;
  else if(module_item.id() == ID_verilog_always_latch)
  {
    throw errort().with_location(module_item.source_location())
      << "no synthesis support for always_latch";
  }
  else
    DATA_INVARIANT(
      false, "unknown always construct: " + module_item.id_string());

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
    throw errort().with_location(module_item.source_location())
      << "initial module item expected to have one operand";
  }

  if(ignore_initial)
    return;

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

Function: verilog_synthesist::synth_asertion_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assertion_item(
  const verilog_assertion_itemt &assertion_item)
{
  // 1800-2017
  // 16.4.3 Deferred assertions outside procedural code
  //
  // module m (input a, b);
  //  a1: assert #0 (a == b);
  // endmodule
  //  ---->
  // module m (input a, b);
  //   always_comb begin
  //     a1: assert #0 (a == b);
  //   end
  // endmodule

  construct = constructt::ALWAYS_COMB;
  event_guard = event_guardt::NONE;

  value_mapt always_value_map;
  value_map = &always_value_map;
  synth_statement(assertion_item.statement());
  value_map = NULL;
}

/*******************************************************************\

Function: verilog_synthesist::make_supply_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::make_supply_value(
  const irep_idt &decl_class,
  const typet &type)
{
  if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    auto element = make_supply_value(decl_class, array_type.element_type());
    return array_of_exprt(element, array_type);
  }
  else if(type.id() == ID_unsignedbv)
  {
    if(decl_class == ID_supply0)
      return from_integer(0, type);
    else
      return from_integer(
        power(2, to_unsignedbv_type(type).get_width()) - 1, type);
  }
  else if(type.id() == ID_signedbv)
  {
    if(decl_class == ID_supply0)
      return from_integer(0, type);
    else
      return from_integer(-1, type);
  }
  else if(type.id() == ID_bool)
  {
    if(decl_class == ID_supply0)
      return false_exprt();
    else
      return true_exprt();
  }
  else
  {
    throw errort() << decl_class << " for unexpected type " << to_string(type);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_decl(const verilog_declt &statement) {
  // Look for supply0 and supply1 port class.
  if(statement.get_class() == ID_supply0 || statement.get_class() == ID_supply1)
  {
    for(auto &declarator : statement.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      auto symbol_expr = declarator.symbol_expr();
      const symbolt &symbol = ns.lookup(symbol_expr);

      if(!symbol.is_state_var)
      {
        // much like a continuous assignment
        const auto value =
          make_supply_value(statement.get_class(), symbol_expr.type());
        verilog_continuous_assignt assign(equal_exprt(symbol_expr, value));
        assign.add_source_location() = declarator.source_location();
        synth_continuous_assign(assign);
      }
    }
  }

  for(auto &declarator : statement.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    auto lhs = declarator.symbol_expr();

    // This is reg x = ... or wire x = ...
    if(declarator.has_value())
    {
      // These are only allowed for module-level declarations,
      // not block-level.
      construct=constructt::INITIAL;
      event_guard=event_guardt::NONE;

      auto rhs = declarator.value();
      const symbolt &symbol = ns.lookup(lhs);

      if(symbol.is_state_var)
      {
        // much like: initial LHS=RHS;
        verilog_initialt initial;
        initial.statement()=verilog_blocking_assignt(lhs, rhs);
        initial.statement().add_source_location() =
          declarator.source_location();
        initial.add_source_location() = declarator.source_location();
        synth_initial(initial);
      }
      else
      {
        // much like a continuous assignment
        verilog_continuous_assignt assign(equal_exprt(lhs, rhs));
        assign.add_source_location() = declarator.source_location();
        synth_continuous_assign(assign);
      }
    }
    else if(initial_zero)
    {
      const symbolt &symbol = ns.lookup(lhs);

      if(symbol.is_state_var)
      {
        // much like: initial LHS=0;
        auto rhs_opt = verilog_default_initializer(lhs.type());
        if(!rhs_opt.has_value())
        {
          throw errort().with_location(declarator.source_location())
            << "cannot default-initialize `" << to_string(lhs) << "'";
        }
        verilog_initialt initial{verilog_blocking_assignt{lhs, *rhs_opt}};
        initial.statement().add_source_location() =
          declarator.source_location();
        initial.add_source_location() = declarator.source_location();
        synth_initial(initial);
      }
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_function_or_task_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_function_or_task_decl(
  const verilog_function_or_task_declt &statement)
{
}

/*******************************************************************\

Function: verilog_synthesist::synth_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_block(const verilog_blockt &statement)
{
  for(auto &block_statement : statement.statements())
    synth_statement(block_statement);
}

/*******************************************************************\

Function: verilog_synthesist::synth_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_continuous_assign(
  const verilog_continuous_assignt &module_item)
{
  construct=constructt::OTHER;

  forall_operands(it, module_item)
  {
    if(it->id()!=ID_equal || it->operands().size()!=2)
    {
      throw errort().with_location(it->source_location())
        << "unexpected continuous assignment";
    }

    // we basically re-write this into an always block:
    // assign x=y;  -->   always @(*) force x=y;
    verilog_forcet assignment;

    assignment.lhs() = to_equal_expr(*it).lhs();
    assignment.rhs() = to_equal_expr(*it).rhs();
    assignment.add_source_location()=module_item.source_location();    
    
    verilog_event_guardt event_guard;
    event_guard.add_source_location()=module_item.source_location();
    event_guard.body() = assignment;

    verilog_always_baset always(
      ID_verilog_always, event_guard, module_item.source_location());
    synth_always_base(always);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_force

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_force(const verilog_forcet &statement)
{
  synth_force_rec(statement.lhs(), statement.rhs());
}

/*******************************************************************\

Function: verilog_synthesist::synth_force

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_force_rec(
  const exprt &lhs,
  const exprt &rhs)
{
  if(lhs.id()==ID_concatenation)
  {
    // split it up
    mp_integer offset = 0;

    // do it from right to left
    
    for(exprt::operandst::const_reverse_iterator
        it=lhs.operands().rbegin();
        it!=lhs.operands().rend();
        it++)
    {
      auto offset_constant = from_integer(offset, natural_typet{});

      if(it->type().id()==ID_bool)
      {
        extractbit_exprt bit_extract(rhs, offset_constant);
        ++offset;
        synth_force_rec(*it, bit_extract);
      }
      else if(it->type().id()==ID_signedbv ||
              it->type().id()==ID_unsignedbv)
      {
        auto width = get_width(it->type());
        extractbits_exprt bit_extract(rhs, offset_constant, it->type());
        synth_force_rec(*it, bit_extract);
        offset+=width;
      }
      else
      {
        throw errort().with_location(it->source_location())
          << "continuous assignment to type `" << to_string(it->type())
          << "' not supported";
      }
    }
    
    return;
  }

  // get symbol
  const symbolt &symbol=assignment_symbol(lhs);

  // turn into combinational assignment
  assignmentt &assignment=assignments[symbol.name];

  if(assignment.type==event_guardt::NONE)
  {
    assignment.type=event_guardt::COMBINATIONAL;
  }
  else if(assignment.type == event_guardt::CLOCK)
  {
    throw errort().with_location(lhs.source_location())
      << "variable " << symbol.display_name() << " is clocked";
  }
  else if(assignment.type == event_guardt::COMBINATIONAL)
  {
    // leave as is
  }
  else
    DATA_INVARIANT(false, "unexpected assignment type");

  // If the symbol is marked as a state variable,
  // turn it into a wire now.
  if(symbol.is_state_var)
  {
    warning().source_location = symbol.location;
    warning() << "Making " << symbol.display_name() << " a wire" << eom;
    symbolt &writeable_symbol = symbol_table_lookup(symbol.name);
    writeable_symbol.is_state_var = false;
  }

  auto lhs_synth = synth_expr(lhs, symbol_statet::CURRENT);
  auto rhs_synth = synth_expr(rhs, symbol_statet::CURRENT);

  equal_exprt equality{std::move(lhs_synth), std::move(rhs_synth)};
  invars.push_back(std::move(equality));
}

/*******************************************************************\

Function: verilog_synthesist::synth_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assign(const verilog_assignt &statement)
{
  if(construct == constructt::OTHER)
  {
    throw errort().with_location(statement.source_location())
      << "unexpected assignment statement";
  }

  exprt lhs = statement.lhs();
  lhs = synth_lhs_expr(lhs);

  exprt rhs = statement.rhs();
  rhs = synth_expr(rhs, symbol_statet::CURRENT);

  irep_idt compound_id = irep_idt{};

  if(statement.id() == ID_verilog_blocking_assign_plus)
    compound_id = ID_plus;
  else if(statement.id() == ID_verilog_blocking_assign_minus)
    compound_id = ID_minus;
  else if(statement.id() == ID_verilog_blocking_assign_mult)
    compound_id = ID_mult;
  else if(statement.id() == ID_verilog_blocking_assign_div)
    compound_id = ID_div;
  else if(statement.id() == ID_verilog_blocking_assign_mod)
    compound_id = ID_mod;
  else if(statement.id() == ID_verilog_blocking_assign_bitand)
    compound_id = ID_bitand;
  else if(statement.id() == ID_verilog_blocking_assign_bitor)
    compound_id = ID_bitor;
  else if(statement.id() == ID_verilog_blocking_assign_bitxor)
    compound_id = ID_bitxor;
  else if(statement.id() == ID_verilog_blocking_assign_lshr)
    compound_id = ID_lshr;
  else if(statement.id() == ID_verilog_blocking_assign_lshl)
    compound_id = ID_shl;
  else if(statement.id() == ID_verilog_blocking_assign_ashr)
    compound_id = ID_ashr;
  else if(statement.id() == ID_verilog_blocking_assign_ashl)
    compound_id = ID_shl;

  if(compound_id != irep_idt{})
  {
    auto lhs_synth = synth_expr(lhs, symbol_statet::CURRENT);
    rhs = binary_exprt{std::move(lhs_synth), compound_id, rhs, rhs.type()};
  }

  // Can the rhs be simplified to a constant, for propagation?
  auto rhs_simplified = simplify_expr(rhs, ns);

  if(rhs_simplified.is_constant())
    rhs = rhs_simplified;

  bool blocking = statement.id() != ID_verilog_non_blocking_assign;

  assignment_rec(lhs, rhs, blocking);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assert_assume_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assert_assume_cover(
  const verilog_assert_assume_cover_statementt &statement)
{
  const irep_idt &identifier = statement.identifier();
  symbolt &symbol=symbol_table_lookup(identifier);

  // This covers both immediate assert/cover and procedural concurrent assert/cover.
  // Cadence SMV assertions are treated as immediate assertions,
  // but this is to be checked.
  // Arguments to procedural concurrent assertions are complex
  // (1800-2017 16.14.6.1)
  {
    exprt cond_for_comment = statement.condition();

    // Are we in an initial or always block?
    if(construct != constructt::INITIAL)
    {
      // one of the 'always' variants -- assertions and assumptions have an implicit 'always'
      if(
        statement.id() != ID_verilog_cover_property &&
        statement.id() != ID_verilog_cover_sequence &&
        statement.id() != ID_verilog_immediate_cover)
      {
        if(cond_for_comment.id() != ID_sva_always)
          cond_for_comment = sva_always_exprt(cond_for_comment);
      }
    }

    // mark 'assume' and 'cover' properties as such
    if(
      statement.id() == ID_verilog_assume_property ||
      statement.id() == ID_verilog_restrict_property ||
      statement.id() == ID_verilog_immediate_assume ||
      statement.id() == ID_verilog_smv_assume)
    {
      cond_for_comment = sva_assume_exprt(cond_for_comment);
    }
    else if(
      statement.id() == ID_verilog_cover_property ||
      statement.id() == ID_verilog_cover_sequence)
    {
      // 'cover' properties are existential
      cond_for_comment = sva_cover_exprt(cond_for_comment);
    }

    symbol.location.set_comment(to_string(cond_for_comment));
  }

  exprt cond;

  // Are we in an initial or always block?
  if(construct == constructt::INITIAL)
  {
    if(
      statement.id() == ID_verilog_immediate_assert ||
      statement.id() == ID_verilog_immediate_assume ||
      statement.id() == ID_verilog_immediate_cover)
    {
      cond = synth_expr(statement.condition(), symbol_statet::CURRENT);
    }
    else
    {
      // procedural concurrent -- evaluated just before the clock tick
      cond = synth_expr(statement.condition(), symbol_statet::SYMBOL);
    }

    // add the guard
    cond = guarded_expr(cond);
  }
  else // one of the 'always' variants
  {
    cond = synth_expr(statement.condition(), symbol_statet::CURRENT);

    // add the guard
    cond = guarded_expr(cond);

    // assertions and assumptions have an implicit 'always'
    if(
      statement.id() != ID_verilog_cover_property &&
      statement.id() != ID_verilog_cover_sequence &&
      statement.id() != ID_verilog_immediate_cover)
    {
      if(cond.id() != ID_sva_always)
        cond = sva_always_exprt(cond);
    }
  }

  // mark 'assume' and 'cover' properties as such
  if(
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_restrict_property ||
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_smv_assume)
  {
    cond = sva_assume_exprt(cond);
  }
  else if(statement.id() == ID_verilog_cover_property)
  {
    // 'cover' properties are existential
    cond = sva_cover_exprt{cond};
  }
  else if(statement.id() == ID_verilog_cover_sequence)
  {
    // 'cover' properties are existential
    cond = sva_cover_exprt{sva_sequence_property_exprt{cond}};
  }

  // 1800-2017 16.12.2 Sequence property
  if(
    statement.id() == ID_verilog_cover_property ||
    statement.id() == ID_verilog_cover_sequence)
  {
    set_default_sequence_semantics(cond, sva_sequence_semanticst::STRONG);
  }
  else
  {
    set_default_sequence_semantics(cond, sva_sequence_semanticst::WEAK);
  }

  symbol.value = std::move(cond);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assert_assume_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assert_assume_cover(
  const verilog_assert_assume_cover_module_itemt &module_item)
{
  // These are static concurrent assert/cover module items.
  const irep_idt &identifier = module_item.identifier();
  symbolt &symbol=symbol_table_lookup(identifier);

  {
    exprt cond_for_comment = module_item.condition();

    if(
      module_item.id() == ID_verilog_assert_property ||
      module_item.id() == ID_verilog_assume_property ||
      module_item.id() == ID_verilog_restrict_property)
    {
      // Concurrent assertions and assumptions come with an implicit 'always'
      // (1800-2017 Sec 16.12.11).
      if(cond_for_comment.id() != ID_sva_always)
        cond_for_comment = sva_always_exprt{cond_for_comment};
    }
    else if(
      module_item.id() == ID_verilog_cover_property ||
      module_item.id() == ID_verilog_cover_sequence)
    {
      // 'cover' requirements are existential.
      cond_for_comment = sva_cover_exprt{cond_for_comment};
    }

    symbol.location.set_comment(to_string(cond_for_comment));
  }

  construct=constructt::OTHER;

  auto cond = synth_expr(module_item.condition(), symbol_statet::SYMBOL);

  if(module_item.id() == ID_verilog_assert_property)
  {
    // Concurrent assertions come with an implicit 'always'
    // (1800-2017 Sec 16.12.11).
    if(cond.id() != ID_sva_always)
      cond = sva_always_exprt{cond};
  }
  else if(
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property)
  {
    // Concurrent assumptions come with an implicit 'always'
    // (1800-2017 Sec 16.12.11).
    if(cond.id() != ID_sva_always)
      cond = sva_always_exprt{cond};

    // mark assumptions
    cond = sva_assume_exprt{cond};
  }
  else if(module_item.id() == ID_verilog_cover_property)
  {
    // 'cover' requirements are existential.
    cond = sva_cover_exprt{cond};
  }
  else if(module_item.id() == ID_verilog_cover_sequence)
  {
    // 'cover' requirements are existential.
    cond = sva_cover_exprt{sva_sequence_property_exprt{cond}};
  }
  else
    PRECONDITION(false);

  // 1800-2017 16.12.2 Sequence property
  if(
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence)
  {
    set_default_sequence_semantics(cond, sva_sequence_semanticst::STRONG);
  }
  else
  {
    set_default_sequence_semantics(cond, sva_sequence_semanticst::WEAK);
  }

  symbol.value = std::move(cond);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assume(
  const verilog_assume_statementt &statement)
{
  construct=constructt::OTHER;

  auto condition = synth_expr(statement.condition(), symbol_statet::CURRENT);

  // add the guard
  condition = guarded_expr(condition);

  // add it as an invariant
  invars.push_back(condition);
}

/*******************************************************************\

Function: verilog_synthesist::synth_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assume(
  const verilog_assert_assume_cover_module_itemt &module_item)
{
  auto condition = synth_expr(to_binary_expr(module_item).op0(), symbol_statet::SYMBOL);

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
  // the pattern has the max type, not the case operand
  const typet &pattern_type=pattern.type();

  // we need to take case of ?, x, z in the pattern
  if(is_aval_bval(pattern_type))
  {
    // We are using masking based on the pattern.
    // The aval is the comparison value, and the
    // negation of bval is the mask.
    auto pattern_aval = ::aval(pattern);
    auto pattern_bval = ::bval(pattern);
    auto mask_expr = bitnot_exprt{pattern_bval};

    auto case_operand_casted = typecast_exprt{
      typecast_exprt::conditional_cast(
        case_operand, aval_bval_underlying(pattern_type)),
      mask_expr.type()};

    return equal_exprt{
      bitand_exprt{case_operand_casted, mask_expr},
      bitand_exprt{pattern_aval, mask_expr}};
  }

  // 2-valued comparison
  exprt case_operand_casted =
    typecast_exprt::conditional_cast(case_operand, pattern_type);

  return equal_exprt(case_operand_casted, pattern);
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
    auto pattern = synth_expr(*it, symbol_statet::CURRENT);
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
    throw errort().with_location(statement.source_location())
      << "case statement expected to have at least one operand";
  }

  // do the argument of the case
  auto case_operand = synth_expr(to_multi_ary_expr(statement).op0(), symbol_statet::CURRENT);
  
  // we convert the rest to if-then-else
  exprt start;
  exprt *last_if=&start;
  std::optional<verilog_statementt> default_case;

  for(unsigned i=1; i<statement.operands().size(); i++)
  {
    const exprt &e=statement.operands()[i];

    if(e.id()!=ID_case_item)
    {
      throw errort() << "expected case_item";
    }

    auto &case_item = to_verilog_case_item(e);

    // default?
    if(case_item.is_default())
      default_case = case_item.case_statement();
    else
    {
      exprt if_statement(ID_if);
      if_statement.reserve_operands(3);
      if_statement.add_to_operands(
        synth_case_values(case_item.case_value(), case_operand));
      if_statement.add_to_operands(case_item.case_statement());

      last_if->add_to_operands(std::move(if_statement));
      last_if = &last_if->operands().back();
    }
  }

  if(default_case.has_value())
  {
    // Attach the 'default' to the final 'if' as 'else'
    last_if->add_to_operands(std::move(default_case.value()));
  }

  // synthesize the new if-then-else

  if(!start.operands().empty())
    synth_statement(
      static_cast<verilog_statementt &>(to_multi_ary_expr(start).op0()));
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
  auto if_cond = synth_expr(statement.cond(), symbol_statet::CURRENT);

  if(if_cond.is_true())
  {
    synth_statement(statement.then_case());
    return;
  }

  // save current value_map pointer
  value_mapt *old_map=value_map;

  // produce new value maps
  value_mapt true_map(*value_map), false_map(*value_map);

  true_map.clear_changed();
  true_map.guard.push_back(if_cond);

  false_map.clear_changed();
  false_map.guard.push_back(not_exprt{if_cond});

  // 'then' case
  {
    value_map=&true_map;
    synth_statement(statement.then_case());
  }

  // 'else' case
  if(statement.has_else_case())
  {
    value_map=&false_map;
    synth_statement(statement.else_case());
  }

  // restore and merge
  value_map=old_map;

  // merge current map
  merge(
    if_cond, true_map.current, false_map.current, false, value_map->current);

  // merge final map
  merge(if_cond, true_map.final, false_map.final, true, value_map->final);
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
    const symbolt &symbol=ns.lookup(it);

    exprt true_value=current_value(true_map, symbol, use_previous_assignments);
    exprt false_value=current_value(false_map, symbol, use_previous_assignments);
    
    // this is a phi-node equivalent
    if_exprt value{guard, true_value, false_value, symbol.type};

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
    throw errort().with_location(statement.source_location())
      << "event_guard expected to have two operands";
  }

  if(event_guard!=event_guardt::NONE)
  {
    throw errort().with_location(statement.source_location())
      << "event guard already specified";
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
        throw errort().with_location(it->source_location())
          << "pos/negedge expected to have one operand";
      }

      irep_idt identifier="conf::clock_enable_mode";

      // check symbol_table for clock guard

      if(symbol_table.symbols.find(identifier)!=symbol_table.symbols.end())
      {
        // found! we make it a guard

        auto &op = to_unary_expr(*it).op();

        if(op.type().id() == ID_bool)
          guards.push_back(op);
        else
        {
          // get LSB
          guards.push_back(extractbit_exprt{op, integer_typet{}.zero_expr()});
        }

        throw errort() << "Notice: using clock guard " << identifier;
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
    throw errort().with_location(statement.source_location())
      << "delay expected to have two operands";
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
    throw errort().with_location(statement.source_location())
      << "for expected to have four operands";
  }

  synth_statement(statement.initialization());

  while(true)
  {
    DATA_INVARIANT(
      statement.condition().type().id() == ID_bool,
      "for condition must be Boolean");

    auto guard_value_opt = synthesis_constant(statement.condition());

    if(!guard_value_opt.has_value())
    {
      throw errort().with_location(statement.condition().source_location())
        << "synthesis failed to evaluate loop guard: `"
        << to_string(statement.condition()) << '\'';
    }

    if(guard_value_opt.value() == 0)
      break;

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
    throw errort().with_location(statement.source_location())
      << statement.id() << " expected to have one operand";
  }

  const auto &op = to_unary_expr(statement).op();

  // stupid implementation
  exprt one = from_integer(1, op.type());

  bool increment =
    statement.id() == ID_preincrement || statement.id() == ID_postincrement;

  exprt rhs;

  if(increment)
    rhs = plus_exprt(op, one);
  else
    rhs = minus_exprt(op, one);

  verilog_blocking_assignt assignment{op, rhs};
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
    throw errort().with_location(statement.source_location())
      << "while expected to have two operands";
  }

  while(true)
  {  
    exprt tmp_guard=statement.condition();
    tmp_guard = typecast_exprt{tmp_guard, bool_typet{}};
    tmp_guard = synth_expr(tmp_guard, symbol_statet::CURRENT);
    simplify(tmp_guard, ns);
 
    if(!tmp_guard.is_constant())
    {
      throw errort().with_location(statement.body().source_location())
        << "synthesis failed to evaluate loop guard: `" << to_string(tmp_guard)
        << '\'';
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
    throw errort().with_location(statement.source_location())
      << "repeat expected to have two operands";
  }

  throw errort().with_location(statement.source_location())
    << "cannot synthesize `repeat'";
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
    throw errort().with_location(statement.source_location())
      << "forever expected to have one operand";
  }

  throw errort().with_location(statement.source_location())
    << "cannot synthesize `forever'";
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
    const symbolt &symbol=ns.lookup(identifier);

    if(symbol.type.id()!=ID_code)
    {
      throw errort().with_location(statement.source_location())
        << "expected function or task as first operand";
    }
    
    const code_typet &code_type=to_code_type(symbol.type);

    const code_typet::parameterst &parameters=
      code_type.parameters();

    const exprt::operandst &actuals = statement.arguments();

    if(parameters.size()!=actuals.size())
    {
      throw errort().with_location(statement.source_location())
        << "wrong number of arguments";
    }
    
    // do assignments to input parameters
    for(unsigned i=0; i<parameters.size(); i++)
    {
      const symbolt &a_symbol=ns.lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_input))
      {
        verilog_blocking_assignt assignment{a_symbol.symbol_expr(), actuals[i]};
        assignment.add_source_location()=statement.source_location();
        synth_statement(assignment);
      }
    }

    synth_statement(to_verilog_statement(symbol.value));

    // do assignments to output parameters
    for(unsigned i=0; i<parameters.size(); i++)
    {
      const symbolt &a_symbol=ns.lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_output))
      {
        verilog_blocking_assignt assignment{actuals[i], a_symbol.symbol_expr()};
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
  else if(statement.id() == ID_break)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of break not supported";
  }
  else if(statement.id()==ID_case ||
          statement.id()==ID_casex ||
          statement.id()==ID_casez)
    synth_case(statement);
  else if(
    statement.id() == ID_verilog_blocking_assign ||
    statement.id() == ID_verilog_blocking_assign_plus ||
    statement.id() == ID_verilog_blocking_assign_minus ||
    statement.id() == ID_verilog_blocking_assign_mult ||
    statement.id() == ID_verilog_blocking_assign_div ||
    statement.id() == ID_verilog_blocking_assign_mod ||
    statement.id() == ID_verilog_blocking_assign_bitand ||
    statement.id() == ID_verilog_blocking_assign_bitor ||
    statement.id() == ID_verilog_blocking_assign_bitxor ||
    statement.id() == ID_verilog_blocking_assign_lshr ||
    statement.id() == ID_verilog_blocking_assign_lshl ||
    statement.id() == ID_verilog_blocking_assign_ashr ||
    statement.id() == ID_verilog_blocking_assign_ashl)
  {
    synth_assign(to_verilog_assign(statement));
  }
  else if(statement.id() == ID_continue)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of continue not supported";
  }
  else if(statement.id() == ID_procedural_continuous_assign)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of procedural continuous assignment not supported";
  }
  else if(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert ||
    statement.id() == ID_verilog_cover_property ||
    statement.id() == ID_verilog_cover_sequence)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_statement(statement));
  }
  else if(
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_restrict_property ||
    statement.id() == ID_verilog_smv_assume)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_statement(statement));
  }
  else if(statement.id() == ID_verilog_expect_property)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of expect property not supported";
  }
  else if(statement.id() == ID_verilog_non_blocking_assign)
    synth_assign(to_verilog_assign(statement));
  else if(statement.id()==ID_force)
    synth_force(to_verilog_force(statement));
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
  else if(statement.id() == ID_return)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of return not supported";
  }
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
    synth_decl(to_verilog_decl(statement));
  }
  else if(
    statement.id() == ID_verilog_function_decl ||
    statement.id() == ID_verilog_task_decl)
  {
  }
  else if(statement.id()==ID_skip)
  {
    // do nothing
  }
  else if(statement.id() == ID_verilog_label_statement)
    synth_statement(to_verilog_label_statement(statement).statement());
  else if(statement.id() == ID_verilog_event_trigger)
  {
    // not synthesized
  }
  else
  {
    throw errort().with_location(statement.source_location())
      << "unexpected statement during synthesis: " << statement.id();
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
  {
    synth_decl(to_verilog_decl(module_item));
  }
  else if(
    module_item.id() == ID_verilog_function_decl ||
    module_item.id() == ID_verilog_task_decl)
  {
    synth_function_or_task_decl(to_verilog_function_or_task_decl(module_item));
  }
  else if(
    module_item.id() == ID_parameter_decl ||
    module_item.id() == ID_local_parameter_decl ||
    module_item.id() == ID_parameter_override)
  {
  }
  else if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
    synth_always_base(to_verilog_always_base(module_item));
  else if(module_item.id()==ID_initial)
    synth_initial(to_verilog_initial(module_item));
  else if(module_item.id()==ID_continuous_assign)
    synth_continuous_assign(to_verilog_continuous_assign(module_item));
  else if(module_item.id()==ID_inst)
    synth_module_instance(to_verilog_inst(module_item), trans);
  else if(module_item.id()==ID_inst_builtin)
    synth_module_instance_builtin(to_verilog_inst_builtin(module_item), trans);
  else if(module_item.id()==ID_generate_block)
  {
    // These are retained to record the scope.
    // Synthesis treats them like a block statement.
    for(auto &block_item :
        to_verilog_generate_block(module_item).module_items())
    {
      synth_module_item(block_item, trans);
    }
  }
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_module_item(module_item));
  }
  else if(
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_module_item(module_item));
  }
  else if(module_item.id() == ID_verilog_assertion_item)
  {
    synth_assertion_item(to_verilog_assertion_item(module_item));
  }
  else if(module_item.id()==ID_task)
  {
    // ignore for now
  }
  else if(module_item.id() == ID_verilog_final)
  {
    // no synthesis semantics
  }
  else if(module_item.id() == ID_verilog_let)
  {
    // done already
  }
  else if(module_item.id() == ID_verilog_empty_item)
  {
  }
  else if(module_item.id() == ID_verilog_package_import)
  {
    // done already
  }
  else if(module_item.id() == ID_verilog_clocking)
  {
  }
  else if(module_item.id() == ID_verilog_covergroup)
  {
  }
  else if(module_item.id() == ID_verilog_default_clocking)
  {
  }
  else if(module_item.id() == ID_verilog_default_disable)
  {
    throw errort().with_location(module_item.source_location())
      << "default disable iff is unsupported";
  }
  else if(module_item.id() == ID_verilog_property_declaration)
  {
  }
  else if(module_item.id() == ID_verilog_sequence_declaration)
  {
  }
  else if(module_item.id() == ID_function_call)
  {
  }
  else
  {
    throw errort().with_location(module_item.source_location())
      << "unexpected module item during synthesis: " << module_item.id();
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
  curr_or_nextt curr_or_next) const
{
  exprt result=exprt(curr_or_next==NEXT?ID_next_symbol:ID_symbol, symbol.type);
  result.set(ID_identifier, symbol.name);

  // The type may need to be lowered
  result.type() = verilog_lowering(result.type());

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
  {
    post_process_wire(symbol.name, new_value);
  }

  auto lhs = symbol_expr(symbol, curr_or_next);

  DATA_INVARIANT(
    lhs.type() == new_value.type(), "synth_assignments type consistency");

  equal_exprt equality_expr{std::move(lhs), new_value};

  constraints.add_to_operands(std::move(equality_expr));
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

    if(
      symbol.is_state_var && !symbol.is_macro && symbol.type.id() != ID_integer)
    {
      assignmentt &assignment=assignments[symbol.name];

      if(assignment.is_cycle_local)
        continue; // ignore

      if(assignment.type==event_guardt::COMBINATIONAL)
      {
        warning().source_location = symbol.location;
        warning() << "Making " << symbol.display_name() << " a wire" << eom;
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

    DATA_INVARIANT(
      assignment.next.value.is_not_nil(), "must have assignment value");

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
  bool use_previous_assignments) const
{
  if(!symbol.is_state_var)
  {
    if(use_previous_assignments)
    {
      // see if we have a previous assignment
      auto assignment_it = assignments.find(symbol.name);
      if(assignment_it != assignments.end())
      {
        const exprt &value = (construct == constructt::INITIAL)
                               ? assignment_it->second.init.value
                               : assignment_it->second.next.value;

        if(value.is_not_nil())
          return value; // done
      }
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
      auto assignment_it = assignments.find(symbol.name);
      if(assignment_it != assignments.end())
      {
        const exprt &value = (construct == constructt::INITIAL)
                               ? assignment_it->second.init.value
                               : assignment_it->second.next.value;

        if(value.is_not_nil())
          return value; // done
      }
    }

    if(
      construct == constructt::ALWAYS || construct == constructt::ALWAYS_FF ||
      construct == constructt::ALWAYS_LATCH ||
      construct == constructt::ALWAYS_COMB)
    {
      return symbol_expr(symbol, CURRENT);
    }
    else if(construct == constructt::INITIAL)
    {
      // Initial state computation, i.e., this is a value _before_ the
      // initial state  -- make it non-deterministic
      exprt result=exprt(ID_nondet_symbol, symbol.type);
      result.set(ID_identifier, symbol.name);
      result.set("initial_value", true);
      return result;
    }
    else
    {
      DATA_INVARIANT(false, "unexpected assignment construct");
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
      exprt &lhs = to_equal_expr(*it).lhs(), &rhs = to_equal_expr(*it).rhs();

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
          it->set(ID_value, ID_true);
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

 Purpose: Turn the verilog_module_exprt into a transition system
          expression

\*******************************************************************/

void verilog_synthesist::convert_module_items(symbolt &symbol)
{
  PRECONDITION(symbol.value.id() == ID_verilog_module);

  const auto &verilog_module = to_verilog_module_expr(symbol.value);

  // clean up
  assignments.clear();
  invars.clear();

  // find out about symbols of this module

  for(auto it=symbol_table.symbol_module_map.lower_bound(module);
      it!=symbol_table.symbol_module_map.upper_bound(module);
      it++)
    local_symbols.insert(it->second);

  // now convert the module items

  transt trans{ID_trans, conjunction({}), conjunction({}), conjunction({}),
               symbol.type};

  for(const auto &module_item : verilog_module.module_items())
    synth_module_item(module_item, trans);

  synth_assignments(trans);
  
  for(const auto & it : invars)
    trans.invar().add_to_operands(it);

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

  symbol.value = std::move(trans);
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
  symbol_table_baset &symbol_table,
  const irep_idt &module,
  verilog_standardt standard,
  bool ignore_initial,
  bool initial_zero,
  message_handlert &message_handler)
{
  const namespacet ns(symbol_table);
  verilog_synthesist verilog_synthesis(
    standard,
    ignore_initial,
    initial_zero,
    ns,
    symbol_table,
    module,
    message_handler);
  return verilog_synthesis.typecheck_main();
}

/*******************************************************************\

Function: verilog_synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_synthesis(
  exprt &expr,
  const irep_idt &module_identifier,
  verilog_standardt standard,
  message_handlert &message_handler,
  const namespacet &ns)
{
  symbol_tablet symbol_table;

  const auto errors_before =
    message_handler.get_message_count(messaget::M_ERROR);

  verilog_synthesist verilog_synthesis(
    standard,
    false,
    false,
    ns,
    symbol_table,
    module_identifier,
    message_handler);

  try
  {
    expr = verilog_synthesis.synth_expr(
      expr, verilog_synthesist::symbol_statet::SYMBOL);
  }

  catch(int e)
  {
    verilog_synthesis.error();
  }

  catch(const char *e)
  {
    verilog_synthesis.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    verilog_synthesis.error() << e << messaget::eom;
  }

  catch(const verilog_typecheck_baset::errort &e)
  {
    if(e.what().empty())
      verilog_synthesis.error();
    else
    {
      verilog_synthesis.error().source_location = e.source_location();
      verilog_synthesis.error() << e.what() << messaget::eom;
    }
  }

  return message_handler.get_message_count(messaget::M_ERROR) != errors_before;
}
