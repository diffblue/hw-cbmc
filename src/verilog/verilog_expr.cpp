/*******************************************************************\

Module: Verilog Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_expr.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_iterator.h>
#include <util/mathematical_types.h>
#include <util/prefix.h>

#include "verilog_initializer.h"
#include "verilog_typecheck_base.h"
#include "verilog_types.h"

verilog_wildcard_equality_exprt::verilog_wildcard_equality_exprt(
  exprt lhs,
  exprt rhs)
  : binary_exprt(
      std::move(lhs),
      ID_verilog_wildcard_equality,
      std::move(rhs),
      verilog_unsignedbv_typet{1})
{
}

typet verilog_declaratort::merged_type(const typet &declaration_type) const
{
  typet result = type();
  typet *p = &result;

  while(p->id() == ID_verilog_unpacked_array ||
        p->id() == ID_verilog_associative_array || p->id() == ID_verilog_queue)
  {
    p = &to_type_with_subtype(*p).subtype();
  }

  DATA_INVARIANT(
    p->is_nil(),
    "merged_type only works on unpacked arrays and associative arrays");

  *p = declaration_type;

  return result;
}

bool function_call_exprt::is_system_function_call() const
{
  return function().id() == ID_symbol &&
         has_prefix(
           id2string(to_symbol_expr(function()).get_identifier()), "$");
}

void verilog_module_sourcet::show(std::ostream &out) const
{
  out << "Module: " << base_name() << '\n';

  out << "  Parameters:\n";

  for(auto &parameter : parameter_port_list())
    out << "    " << parameter.pretty() << '\n';

  out << '\n';

  out << "  Ports:\n";

  for(auto &port : ports())
    out << "    " << port.pretty() << '\n';

  out << '\n';

  out << "  Module items:\n";

  for(auto &item : module_items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

static void
dependencies_rec(const verilog_module_itemt &, std::vector<irep_idt> &);

static void dependencies_rec(const exprt &expr, std::vector<irep_idt> &dest)
{
  for(const_depth_iteratort it = expr.depth_cbegin(); it != expr.depth_cend();
      ++it)
  {
    if(it->id() == ID_verilog_package_scope)
    {
      auto &package_scope_expr = to_verilog_package_scope_expr(*it);
      dest.push_back(
        verilog_package_identifier(package_scope_expr.package_base_name()));
    }
  }
}

static void dependencies_rec(const typet &type, std::vector<irep_idt> &dest)
{
  if(type.id() == ID_verilog_package_scope)
  {
    auto &package_scope_type = to_verilog_package_scope_type(type);
    dest.push_back(
      verilog_package_identifier(package_scope_type.package_base_name()));
  }
}

static void dependencies_rec(
  const verilog_module_itemt &module_item,
  std::vector<irep_idt> &dest)
{
  if(module_item.id() == ID_inst)
  {
    dest.push_back(
      verilog_module_symbol(to_verilog_inst(module_item).get_module()));
  }
  else if(module_item.id() == ID_generate_block)
  {
    for(auto &sub_item : to_verilog_generate_block(module_item).module_items())
      dependencies_rec(sub_item, dest);
  }
  else if(module_item.id() == ID_generate_if)
  {
    auto &generate_if = to_verilog_generate_if(module_item);
    dependencies_rec(generate_if.then_case(), dest);
    if(generate_if.has_else_case())
      dependencies_rec(generate_if.else_case(), dest);
  }
  else if(module_item.id() == ID_generate_for)
  {
    dependencies_rec(to_verilog_generate_for(module_item).body(), dest);
  }
  else if(module_item.id() == ID_verilog_package_import)
  {
    for(auto &import_item : module_item.get_sub())
    {
      dest.push_back(
        verilog_package_identifier(import_item.get(ID_verilog_package)));
    }
  }
  else if(module_item.id() == ID_parameter_decl)
  {
    auto &parameter_decl = to_verilog_parameter_decl(module_item);
    for(auto &declarator : parameter_decl.declarators())
    {
      dependencies_rec(declarator.type(), dest);
      dependencies_rec(declarator.value(), dest);
    }
  }
  else if(module_item.id() == ID_local_parameter_decl)
  {
    auto &localparam_decl = to_verilog_local_parameter_decl(module_item);
    for(auto &declarator : localparam_decl.declarators())
    {
      dependencies_rec(declarator.type(), dest);
      dependencies_rec(declarator.value(), dest);
    }
  }
  else if(module_item.id() == ID_decl)
  {
    auto &decl = to_verilog_decl(module_item);
    dependencies_rec(decl.type(), dest);
    for(auto &declarator : decl.declarators())
    {
      dependencies_rec(declarator.type(), dest);
      dependencies_rec(declarator.value(), dest);
    }
  }
  else if(
    module_item.id() == ID_verilog_function_decl ||
    module_item.id() == ID_verilog_task_decl)
  {
  }
  else if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
  {
    dependencies_rec(to_verilog_always_base(module_item).statement(), dest);
  }
  else if(module_item.id() == ID_initial)
  {
    dependencies_rec(to_verilog_initial(module_item).statement(), dest);
  }
  else if(module_item.id() == ID_inst)
  {
  }
  else if(module_item.id() == ID_inst_builtin)
  {
  }
  else if(module_item.id() == ID_continuous_assign)
  {
  }
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence)
  {
  }
  else if(module_item.id() == ID_verilog_assertion_item)
  {
  }
  else if(module_item.id() == ID_parameter_override)
  {
  }
  else if(module_item.id() == ID_verilog_final)
  {
  }
  else if(module_item.id() == ID_verilog_let)
  {
    // to_verilog_let(module_item));
  }
  else if(module_item.id() == ID_verilog_smv_assume)
  {
  }
  else if(module_item.id() == ID_verilog_property_declaration)
  {
    // to_verilog_property_declaration(module_item)
  }
  else if(module_item.id() == ID_verilog_sequence_declaration)
  {
    // to_verilog_sequence_declaration(module_item)
  }
}

std::vector<irep_idt> verilog_item_containert::dependencies() const
{
  std::vector<irep_idt> result;

  for(auto &item : items())
    dependencies_rec(item, result);

  return result;
}

void verilog_checkert::show(std::ostream &out) const
{
  out << "Checker: " << base_name() << '\n';

  out << "  Ports:\n";

  for(auto &port : ports())
    out << "    " << port.pretty() << '\n';

  out << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

void verilog_packaget::show(std::ostream &out) const
{
  out << "Pacakge: " << base_name() << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

void verilog_programt::show(std::ostream &out) const
{
  out << "Program: " << base_name() << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

void verilog_classt::show(std::ostream &out) const
{
  out << "Class: " << base_name() << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

void verilog_interfacet::show(std::ostream &out) const
{
  out << "Interface: " << base_name() << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

void verilog_udpt::show(std::ostream &out) const
{
  out << "UDP: " << base_name() << '\n';

  out << "  Items:\n";

  for(auto &item : items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

static exprt lower(const verilog_non_indexed_part_select_exprt &part_select)
{
  auto get_width = [](const typet &t) -> mp_integer
  {
    if(t.id() == ID_bool)
      return 1;

    if(
      t.id() == ID_unsignedbv || t.id() == ID_signedbv ||
      t.id() == ID_verilog_signedbv || t.id() == ID_verilog_unsignedbv)
    {
      return to_bitvector_type(t).get_width();
    }

    PRECONDITION(false);
  };

  auto &src = part_select.src();

  auto op1 = numeric_cast_v<mp_integer>(to_constant_expr(part_select.msb()));
  auto op2 = numeric_cast_v<mp_integer>(to_constant_expr(part_select.lsb()));

  mp_integer src_width = get_width(src.type());
  mp_integer src_offset = string2integer(src.type().get_string(ID_C_offset));

  // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
  // x for 4-state and 0 for 2-state values. We
  // achieve that by padding the operand from either end,
  // or both.
  exprt src_padded = src;

  if(op2 < src_offset)
  {
    // lsb too small, pad below
    auto padding_width = src_offset - op2;
    auto padding = from_integer(
      0, unsignedbv_typet{numeric_cast_v<std::size_t>(padding_width)});
    auto new_type = unsignedbv_typet{numeric_cast_v<std::size_t>(
      get_width(src_padded.type()) + padding_width)};
    src_padded = concatenation_exprt(src_padded, padding, new_type);
    op2 += padding_width;
    op1 += padding_width;
  }

  if(op1 >= src_width + src_offset)
  {
    // msb too large, pad above
    auto padding_width = op1 - (src_width + src_offset) + 1;
    auto padding = from_integer(
      0, unsignedbv_typet{numeric_cast_v<std::size_t>(padding_width)});
    auto new_type = unsignedbv_typet{numeric_cast_v<std::size_t>(
      get_width(src_padded.type()) + padding_width)};
    src_padded = concatenation_exprt(padding, src_padded, new_type);
  }

  op2 -= src_offset;
  op1 -= src_offset;

  // Construct the extractbits expression
  return extractbits_exprt{
    src_padded, from_integer(op2, integer_typet()), part_select.type()}
    .with_source_location(part_select.source_location());
}

exprt verilog_non_indexed_part_select_exprt::lower() const
{
  return ::lower(*this);
}

static exprt
lower(const verilog_indexed_part_select_plus_or_minus_exprt &part_select)
{
  auto get_width = [](const typet &t) -> mp_integer
  {
    if(t.id() == ID_bool)
      return 1;

    if(
      t.id() == ID_unsignedbv || t.id() == ID_signedbv ||
      t.id() == ID_verilog_signedbv || t.id() == ID_verilog_unsignedbv)
    {
      return to_bitvector_type(t).get_width();
    }

    PRECONDITION(false);
  };

  PRECONDITION(
    part_select.id() == ID_verilog_indexed_part_select_plus ||
    part_select.id() == ID_verilog_indexed_part_select_minus);

  const exprt &src = part_select.src();

  mp_integer src_width = get_width(src.type());
  mp_integer src_offset = string2integer(src.type().get_string(ID_C_offset));

  // The width of the indexed part select must be an
  // elaboration-time constant.
  auto width =
    numeric_cast_v<mp_integer>(to_constant_expr(part_select.width()));

  // The index need not be a constant.
  const exprt &index = part_select.index();

  if(index.is_constant())
  {
    auto index_int = numeric_cast_v<mp_integer>(to_constant_expr(index));

    // Construct the extractbits expression
    mp_integer bottom;

    if(part_select.id() == ID_verilog_indexed_part_select_plus)
    {
      bottom = index_int - src_offset;
    }
    else // ID_verilog_indexed_part_select_minus
    {
      bottom = bottom - width + 1;
    }

    return extractbits_exprt{
      std::move(src), from_integer(bottom, integer_typet{}), part_select.type()}
      .with_source_location(part_select);
  }
  else
  {
    // Index not constant.
    // Use logical right-shift followed by (constant) extractbits.
    auto index_adjusted =
      minus_exprt{index, from_integer(src_offset, index.type())};

    auto src_shifted = lshr_exprt(src, index_adjusted);

    return extractbits_exprt{
      std::move(src_shifted),
      from_integer(0, integer_typet{}),
      part_select.type()}
      .with_source_location(part_select);
  }
}

exprt verilog_indexed_part_select_plus_or_minus_exprt::lower() const
{
  return ::lower(*this);
}

exprt verilog_streaming_concatenation_exprt::lower() const
{
  if(id() == ID_verilog_streaming_concatenation_left_to_right)
  {
    // slice size does not matter
    if(stream_expressions().size() == 1)
      return stream_expressions().front();
    else
      PRECONDITION(false);
  }
  else if(id() == ID_verilog_streaming_concatenation_right_to_left)
  {
    if(stream_expressions().size() == 1)
    {
      if(stream_expressions().front().type().id() == ID_bool)
        return stream_expressions().front();
      else
      {
        auto slice_size_int =
          has_slice_size()
            ? numeric_cast_v<std::size_t>(to_constant_expr(slice_size()))
            : std::size_t(1);
        if(slice_size_int == 1)
          return bitreverse_exprt{stream_expressions().front()};
        else
          return bswap_exprt{stream_expressions().front(), slice_size_int};
      }
    }
    else
      PRECONDITION(false);
  }
  else
    PRECONDITION(false);
}

exprt verilog_inside_exprt::lower() const
{
  exprt::operandst disjuncts;

  for(auto &range : range_list())
  {
    if(range.id() == ID_verilog_value_range)
    {
      auto &range_expr = to_verilog_value_range_expr(range);
      DATA_INVARIANT(
        op().type() == range_expr.lhs().type(),
        "inside_exprt type consistency");
      DATA_INVARIANT(
        op().type() == range_expr.rhs().type(),
        "inside_exprt type consistency");
      disjuncts.push_back(and_exprt{
        binary_relation_exprt{op(), ID_ge, range_expr.lhs()},
        binary_relation_exprt{op(), ID_le, range_expr.rhs()}});
    }
    else
    {
      DATA_INVARIANT(
        op().type() == range.type(), "inside_exprt type consistency");
      auto &range_type = range.type();
      if(
        range_type.id() == ID_verilog_unsignedbv ||
        range_type.id() == ID_verilog_signedbv)
      {
        disjuncts.push_back(typecast_exprt{
          verilog_wildcard_equality_exprt{op(), range}, bool_typet()});
      }
      else
        disjuncts.push_back(equal_exprt{op(), range});
    }
  }

  return disjunction(disjuncts);
}

exprt verilog_past_exprt::default_value() const
{
  auto value_opt = verilog_default_initializer(type());
  CHECK_RETURN(value_opt.has_value());
  return *value_opt;
}
