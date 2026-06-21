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

#include <ebmc/ebmc_error.h>

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
    return synth_expr(instance.declaration().cond(), symbol_state);
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
  else if(expr.id() == ID_verilog_bit_select)
  {
    // Lower to extractbit or index, then process the result.
    return synth_lhs_expr(verilog_lowering(std::move(expr)));
  }
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    member_expr.struct_op() = synth_lhs_expr(member_expr.struct_op());
    return expr;
  }
  else if(expr.id() == ID_typecast)
  {
    auto &typecast_expr = to_typecast_expr(expr);
    typecast_expr.op() = synth_lhs_expr(typecast_expr.op());
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

  if(expr.lhs().type().id() != ID_verilog_module_instance)
  {
    throw errort().with_location(expr.source_location())
      << "synthesis expected module instance on lhs of `.', but got `"
      << to_string(expr.lhs().type()) << '\'';
  }

  const irep_idt &lhs_identifier = to_symbol_expr(expr.lhs()).get_identifier();

  // rhs
  const irep_idt &rhs_base_name = expr.rhs().base_name();

  // just patch together

  irep_idt full_identifier =
    id2string(lhs_identifier) + '.' + id2string(rhs_base_name);

  // Note: the instance copy may not yet be in symbol table,
  // as the inst module item may be later.
  // The type checker already checked that it's fine.

  symbol_exprt new_symbol{full_identifier, expr.type()};
  new_symbol.add_source_location()=expr.source_location();
  expr.swap(new_symbol);
}

/*******************************************************************\

Function: verilog_synthesist::replace_by_wire
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::replace_by_wire(exprt &what, const symbolt &base)
{
  PRECONDITION(what.is_not_nil());

  symbolt new_symbol;

  do
  {
    unsigned c = temporary_counter++;
    new_symbol.name = id2string(base.name) + "_aux" + std::to_string(c);
    new_symbol.base_name =
      id2string(base.base_name) + "_aux" + std::to_string(c);
  } while(symbol_table.symbols.find(new_symbol.name) !=
          symbol_table.symbols.end());

  new_symbol.type = what.type();
  new_symbol.module = base.module;
  new_symbol.mode = base.mode;
  new_symbol.location = base.location;
  new_symbol.value = nil_exprt();
  new_symbol.is_auxiliary = true;
  new_symbol.pretty_name = strip_verilog_root_prefix(new_symbol.name);

  symbol_exprt symbol_expr(new_symbol.name, new_symbol.type);

  assignmentt &assignment = assignments[new_symbol.name];
  assignment.next.value = what;
  new_wires.insert(new_symbol.name);

  if(symbol_table.add(new_symbol))
  {
    throw errort() << "failed to add replace_by_wire symbol";
  }

  what = symbol_expr;
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

    if(from > to)
      std::swap(from, to);

    member.push_back(mp_integer());

    // now add the indexes in the range
    for(mp_integer i = from; i <= to; ++i)
    {
      // do the value
      member.back() = i;
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
  else if(lhs.id() == ID_typecast)
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

bool verilog_synthesist::disjoint(const membert &a, const membert &b)
{
  membert::const_iterator a_it = a.begin();
  membert::const_iterator b_it = b.begin();

  while(a_it != a.end() && b_it != b.end())
  {
    if(*a_it != *b_it)
      return true;
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
    else if(e->id() == ID_verilog_bit_select)
    {
      e = &to_verilog_bit_select_expr(*e).src();
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
    else if(e->id() == ID_typecast)
    {
      e = &to_typecast_expr(*e).op();
    }
    else
    {
      throw errort().with_location(e->source_location())
        << "synthesis: failed to get identifier";
    }
  }
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

  event_guard = event_guardt::NONE;

  value_mapt always_value_map;
  DATA_INVARIANT(value_map == nullptr, "always/initial must not nest");
  value_map = &always_value_map;

  synth_statement(module_item.statement());

  for(const auto &it : value_map->final.changed)
  {
    assignmentt &assignment = assignments[it];
    assignment.next.value = value_map->final.symbol_map[it];
    assignment.next.move_assignments();
  }

  value_map = NULL;
}

/*******************************************************************\

Function: verilog_synthesist::synth_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_initial(const verilog_initialt &module_item)
{
  if(module_item.operands().size() != 1)
  {
    throw errort().with_location(module_item.source_location())
      << "initial module item expected to have one operand";
  }

  if(ignore_initial)
    return;

  construct = constructt::INITIAL;
  event_guard = event_guardt::NONE;

  value_mapt initial_value_map;
  DATA_INVARIANT(value_map == nullptr, "always/initial must not nest");
  value_map = &initial_value_map;

  synth_statement(module_item.statement());

  for(const auto &it : value_map->final.changed)
  {
    assignmentt &assignment = assignments[it];
    assignment.init.value = value_map->final.symbol_map[it];
    assignment.init.move_assignments();
  }

  value_map = NULL;
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
  DATA_INVARIANT(value_map == nullptr, "always/initial must not nest");
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

      if(!symbol.is_lvalue)
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

    local_symbols.insert(lhs.get_identifier());

    // This is reg x = ... or wire x = ...
    if(declarator.has_value())
    {
      // These are only allowed for module-level declarations,
      // not block-level.
      construct=constructt::INITIAL;
      event_guard=event_guardt::NONE;

      auto rhs = declarator.value();
      const symbolt &symbol = ns.lookup(lhs);

      if(symbol.is_lvalue)
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

      if(symbol.is_lvalue)
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

Function: verilog_synthesist::synth_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_continuous_assign(
  const verilog_continuous_assignt &module_item)
{
  construct = constructt::OTHER;

  forall_operands(it, module_item)
  {
    if(it->id() != ID_equal || it->operands().size() != 2)
    {
      throw errort().with_location(it->source_location())
        << "unexpected continuous assignment";
    }

    // we basically re-write this into an always block:
    // assign x=y;  -->   always @(*) force x=y;
    verilog_forcet assignment;

    assignment.lhs() = to_equal_expr(*it).lhs();
    assignment.rhs() = to_equal_expr(*it).rhs();
    assignment.add_source_location() = module_item.source_location();

    verilog_event_guardt event_guard;
    event_guard.add_source_location() = module_item.source_location();
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

void verilog_synthesist::synth_force_rec(const exprt &lhs, const exprt &rhs)
{
  if(lhs.id() == ID_concatenation)
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
  if(symbol.is_lvalue)
  {
    warning().source_location = symbol.location;
    warning() << "Making " << symbol.display_name() << " a wire" << eom;
    symbolt &writeable_symbol = symbol_table_lookup(symbol.name);
    writeable_symbol.is_lvalue = false;
  }

  auto lhs_synth = synth_expr(lhs, symbol_statet::CURRENT);
  auto rhs_synth = synth_expr(rhs, symbol_statet::CURRENT);

  equal_exprt equality{std::move(lhs_synth), std::move(rhs_synth)};
  invars.push_back(std::move(equality));
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
      statement.id() == ID_verilog_immediate_cover ||
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
  else if(
    statement.id() == ID_verilog_immediate_cover ||
    statement.id() == ID_verilog_cover_property)
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

  // defaults apply
  apply_defaults(cond);

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
    auto decl_class = to_verilog_decl(module_item).get_class();

    if(decl_class == ID_function || decl_class == ID_task)
    {
      synth_function_or_task_decl(
        to_verilog_function_or_task_decl(module_item));
    }
    else
      synth_decl(to_verilog_decl(module_item));
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
    auto &block_items = to_verilog_generate_block(module_item).module_items();

    // These may have separate default disable iff conditions.
    auto old_default_disable_iff = default_disable_iff;
    default_disable_iff = {};

    for(auto &block_item : block_items)
      find_defaults(block_item);

    // These are retained to record the scope.
    // Synthesis treats them like a block statement.
    for(auto &block_item : block_items)
    {
      synth_module_item(block_item, trans);
    }

    // restore previous default disable iff
    default_disable_iff = old_default_disable_iff;
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
    // handled by find_defaults
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
  else if(module_item.id() == ID_verilog_timeunit)
  {
  }
  else if(module_item.id() == ID_verilog_timeprecision)
  {
  }
  else
  {
    throw errort().with_location(module_item.source_location())
      << "unexpected module item during synthesis: " << module_item.id();
  }
}

/*******************************************************************\

Function: verilog_synthesist::find_defaults

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::find_defaults(const verilog_module_itemt &module_item)
{
  if(module_item.id() == ID_verilog_default_clocking)
  {
  }
  else if(module_item.id() == ID_verilog_default_disable)
  {
    if(default_disable_iff.has_value())
    {
      // it's an error to set the default more than once
      throw errort().with_location(module_item.source_location())
        << "default disable iff already set";
    }
    else
    {
      default_disable_iff = to_verilog_default_disable(module_item).cond();
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::apply_defaults

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::apply_defaults(exprt &expr)
{
  if(default_disable_iff.has_value() && expr.id() != ID_sva_disable_iff)
  {
    expr = sva_disable_iff_exprt{default_disable_iff.value(), std::move(expr)};
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
  if(!symbol.is_lvalue)
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

    if(symbol.is_lvalue && !symbol.is_macro && symbol.type.id() != ID_integer)
    {
      assignmentt &assignment=assignments[symbol.name];

      if(assignment.is_cycle_local)
        continue; // ignore

      if(assignment.type==event_guardt::COMBINATIONAL)
      {
        warning().source_location = symbol.location;
        warning() << "Making " << symbol.display_name() << " a wire" << eom;
        symbol.is_lvalue = false;
      }

      if(symbol.is_lvalue)
      {
        // only state variables can be initialized

        if(!assignment.init.value.is_nil())
          synth_assignments(symbol, CURRENT,
                            assignment.init.value,
                            trans.op1());

        synth_assignments(symbol, NEXT,
                          assignment.next.value,
                          trans.op2());

        // This is a proper state variable
        symbol.is_state_var = true;
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
  if(!symbol.is_lvalue)
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

  // Add port-declared symbols to local_symbols, since ANSI-style
  // port declarations do not appear as decl module items.
  // Don't do for $root, which uses input identifiers of its submodules.
  if(symbol.name != verilog_root_module_identifier())
  {
    for(const auto &port : to_module_type(symbol.type).ports())
      local_symbols.insert(port.identifier());
  }

  // now convert the module items

  transt trans{ID_trans, conjunction({}), conjunction({}), conjunction({}),
               symbol.type};

  // first find any default disable iff at this level
  for(const auto &module_item : verilog_module.module_items())
    find_defaults(module_item);

  // now synthesise
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

Function: verilog_synthesist::synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

transt verilog_synthesist::synthesis()
{
  symbolt &symbol=symbol_table_lookup(module);

  // done already?
  if(symbol.value.id() != ID_trans)
  {
    convert_module_items(symbol);
    CHECK_RETURN(symbol.value.id() == ID_trans);
  }

  return to_trans_expr(symbol.value);
}

/*******************************************************************\

Function: verilog_synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

transt verilog_synthesis(
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

  try
  {
    return verilog_synthesis.synthesis();
  }
  catch(verilog_synthesist::errort error)
  {
    messaget message{message_handler};

    if(error.what().empty())
      message.error();
    else
    {
      message.error().source_location = error.source_location();
      message.error() << error.what() << messaget::eom;
    }

    throw ebmc_errort{};
  }
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
