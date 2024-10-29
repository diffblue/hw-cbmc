/*******************************************************************\

Module: Verilog Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_expr.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/prefix.h>

#include "verilog_typecheck_base.h"

typet verilog_declaratort::merged_type(const typet &declaration_type) const
{
  typet result = type();
  typet *p = &result;

  while(p->id() == ID_verilog_unpacked_array)
    p = &to_type_with_subtype(*p).subtype();

  DATA_INVARIANT(p->is_nil(), "merged_type only works on unpacked arrays");
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
}

std::vector<irep_idt> verilog_item_containert::dependencies() const
{
  std::vector<irep_idt> result;

  for(auto &item : items())
    dependencies_rec(item, result);

  return result;
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
