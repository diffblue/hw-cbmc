/*******************************************************************\

Module: VHDL Expression Printer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// VHDL Expression Printer
///
/// Prints the lowered (CBMC-typed) expressions of the VHDL front-end in
/// VHDL syntax, for traces, --show-trans and messages. The VHDL type
/// names and index ranges are taken from the comments that the
/// lowering records on the CBMC types. Properties use the PSL
/// operators.

#include "expr2vhdl.h"
#include "expr2vhdl_class.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/std_expr.h>

#include <cstdlib>
#include <optional>
#include <sstream>

// IEEE 1076-2008 9.1: the precedence of the operators, highest first
enum vhdl_precedencet : unsigned
{
  PRECEDENCE_PRIMARY = 22,
  PRECEDENCE_MISC = 20,     // **, abs, not
  PRECEDENCE_MULT = 18,     // *, /, mod, rem
  PRECEDENCE_SIGN = 16,     // unary +, -
  PRECEDENCE_ADD = 14,      // +, -, &
  PRECEDENCE_SHIFT = 12,    // sll, srl, sla, sra, rol, ror
  PRECEDENCE_RELATION = 10, // =, /=, <, <=, >, >=
  PRECEDENCE_LOGICAL = 8,   // and, or, xor, nand, nor, xnor
  PRECEDENCE_IMPLIES = 6,   // PSL ->
  PRECEDENCE_IFF = 4,       // PSL <->
  PRECEDENCE_TEMPORAL = 2   // always, eventually!, next, until
};

/// the operand, in parentheses if it binds less tightly
std::string expr2vhdlt::convert_operand(const exprt &op, unsigned precedence)
{
  unsigned p;
  std::string dest = convert(op, p);
  if(precedence > p)
    return '(' + dest + ')';
  else
    return dest;
}

std::string expr2vhdlt::convert_binary(
  const exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  if(src.operands().size() < 2)
    return convert_norep(src, precedence);

  std::string dest;

  for(auto &op : src.operands())
  {
    if(!dest.empty())
      dest += ' ' + symbol + ' ';
    dest += convert_operand(op, precedence);
  }

  return dest;
}

/// IEEE 1076-2008 9.1: the logical operators have the same precedence,
/// and cannot be mixed without parentheses; operands that are logical
/// operators are parenthesised
std::string expr2vhdlt::convert_logical(
  const exprt &src,
  const std::string &symbol,
  unsigned &precedence)
{
  if(src.operands().size() < 2)
    return convert_norep(src, precedence);

  precedence = PRECEDENCE_LOGICAL;
  std::string dest;

  for(auto &op : src.operands())
  {
    if(!dest.empty())
      dest += ' ' + symbol + ' ';
    dest += convert_operand(op, PRECEDENCE_LOGICAL + 1);
  }

  return dest;
}

std::string expr2vhdlt::convert_unary(
  const unary_exprt &src,
  const std::string &symbol,
  unsigned precedence)
{
  return symbol + convert_operand(src.op(), precedence);
}

/// IEEE 1076-2008 10.5.3: there are no conditional expressions in VHDL;
/// we use the syntax of conditional assignments
std::string expr2vhdlt::convert_if(const if_exprt &src)
{
  return "(" + convert(src.true_case()) + " when " + convert(src.cond()) +
         " else " + convert(src.false_case()) + ")";
}

std::string expr2vhdlt::convert_with(const with_exprt &src, unsigned precedence)
{
  if(src.operands().size() < 3)
    return convert_norep(src, precedence);

  // the object, with elements replaced
  std::string dest = "(" + convert(src.old());

  for(std::size_t i = 1; i + 1 < src.operands().size(); i += 2)
  {
    auto &where = src.operands()[i];
    dest += " with ";
    if(where.id() == ID_member_name)
      dest += id2string(where.get(ID_component_name));
    else
      dest += convert(where);
    dest += " => " + convert(src.operands()[i + 1]);
  }

  dest += ")";

  return dest;
}

std::string
expr2vhdlt::convert_update_bit(const update_bit_exprt &src, unsigned)
{
  return "(" + convert(src.src()) + " with " + convert(src.index()) + " => " +
         convert(src.new_value()) + ")";
}

/// IEEE 1076-2008 9.2.5: & is the concatenation operator
std::string expr2vhdlt::convert_concatenation(
  const concatenation_exprt &src,
  unsigned precedence)
{
  return convert_binary(src, "&", precedence);
}

/// an aggregate with a range choice, (1 to n => value)
std::string expr2vhdlt::convert_replication(
  const replication_exprt &src,
  unsigned precedence)
{
  return "(1 to " + convert(src.times()) + " => " + convert(src.op()) + ")";
}

std::string
expr2vhdlt::convert_typecast(const typecast_exprt &src, unsigned &precedence)
{
  // IEEE 1076-2008 9.3.6: a type conversion, when the VHDL type is
  // known; the conversions between closely related types and the
  // conversion functions of numeric_std are both shown as conversions
  auto vhdl_type = src.type().get(ID_C_vhdl_type);

  if(vhdl_type.empty())
    return convert(src.op(), precedence);

  precedence = PRECEDENCE_PRIMARY;
  return id2string(vhdl_type) + "(" + convert(src.op()) + ")";
}

/// IEEE 1076-2008 8.4: an indexed name
std::string
expr2vhdlt::convert_index(const index_exprt &src, unsigned precedence)
{
  return convert_operand(src.array(), precedence) + '(' + convert(src.index()) +
         ')';
}

/// IEEE 1076-2008 8.4: an indexed name of a vector. The index is the
/// bit position, counting from the right-most bit; when the vector has
/// a declared VHDL index range, it is mapped to the index.
std::string
expr2vhdlt::convert_extractbit(const extractbit_exprt &src, unsigned precedence)
{
  std::string dest = convert_operand(src.src(), precedence);

  auto &vector_type = src.src().type();
  auto direction = vector_type.get(ID_C_vhdl_direction);

  if(direction.empty())
    return dest + '[' + convert(src.index()) + ']';

  auto right = string2integer(vector_type.get_string(ID_C_vhdl_right));

  if(src.index().is_constant())
  {
    auto bit = numeric_cast_v<mp_integer>(to_constant_expr(src.index()));
    return dest + '(' +
           integer2string(
             direction == ID_vhdl_downto ? bit + right : right - bit) +
           ')';
  }
  else if(direction == ID_vhdl_downto)
  {
    if(right == 0)
      return dest + '(' + convert(src.index()) + ')';
    else
      return dest + '(' + convert(src.index()) + " + " + integer2string(right) +
             ')';
  }
  else
    return dest + '(' + integer2string(right) + " - " + convert(src.index()) +
           ')';
}

std::string expr2vhdlt::convert_extractbits(
  const extractbits_exprt &src,
  unsigned precedence)
{
  unsigned p;
  std::string op = convert(src.src(), p);

  std::string dest;
  if(precedence > p)
    dest += '(';
  dest += op;
  if(precedence > p)
    dest += ')';

  auto width = to_bitvector_type(src.type()).get_width();

  // IEEE 1076-2008 8.5: a null slice
  if(width == 0)
  {
    dest += "(1 to 0)";
    return dest;
  }

  // The bits of the slice are index to index + width - 1, counting
  // from the right-most bit of the vector. When the vector has a
  // declared VHDL index range, the bit positions are mapped to indices:
  // for v(l downto r), bit b has index b + r; for v(l to r), it has
  // index r - b.
  auto &vector_type = src.src().type();
  auto direction = vector_type.get("#vhdl_direction");

  std::optional<mp_integer> index_int;
  if(src.index().is_constant())
    index_int = numeric_cast_v<mp_integer>(to_constant_expr(src.index()));

  auto bound = [&](const mp_integer &offset) -> std::string
  {
    if(index_int.has_value())
      return integer2string(*index_int + offset);
    else if(offset == 0)
      return convert(src.index());
    else
      return convert(src.index()) + " + " + integer2string(offset);
  };

  if(direction.empty())
  {
    // no VHDL range known; print the bit positions
    dest += '[' + bound(width - 1) + ':' + bound(0) + ']';
  }
  else
  {
    auto right = string2integer(vector_type.get_string("#vhdl_right"));

    if(direction == "vhdl_downto")
    {
      // index = bit + right
      dest += '(' + bound(right + width - 1) + " downto " + bound(right) + ')';
    }
    else
    {
      // index = right - bit; the slice is (right - (index + width - 1)
      // to right - index), which needs the negated index
      std::string low, high;
      if(index_int.has_value())
      {
        low = integer2string(right - *index_int - width + 1);
        high = integer2string(right - *index_int);
      }
      else
      {
        low = integer2string(right - width + 1) + " - " + convert(src.index());
        high = integer2string(right) + " - " + convert(src.index());
      }
      dest += '(' + low + " to " + high + ')';
    }
  }

  return dest;
}

/// IEEE 1076-2008 8.3: a selected name
std::string
expr2vhdlt::convert_member(const member_exprt &src, unsigned precedence)
{
  return convert_operand(src.compound(), precedence) + '.' +
         id2string(src.get_component_name());
}

/// expressions without a VHDL representation, in a compact form
std::string expr2vhdlt::convert_norep(const exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;

  std::string dest = id2string(src.id()) + '(';

  bool first = true;
  for(auto &op : src.operands())
  {
    if(first)
      first = false;
    else
      dest += ", ";
    dest += convert(op);
  }

  return dest + ')';
}

std::string
expr2vhdlt::convert_symbol(const symbol_exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;
  return id2string(src.get_identifier());
}

std::string
expr2vhdlt::convert_nondet_symbol(const exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;
  return "nondet(" + id2string(src.get(ID_identifier)) + ")";
}

std::string
expr2vhdlt::convert_next_symbol(const exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;
  return "next(" + id2string(src.get(ID_identifier)) + ")";
}

/// IEEE 1076-2008 15.5, 15.6, 15.7: numeric, character and string
/// literals; the VHDL type is recorded on the lowered type
std::string
expr2vhdlt::convert_constant(const constant_exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;

  const typet &type = src.type();
  const std::string &value = id2string(src.get_value());

  auto vhdl_type = type.get(ID_C_vhdl_type);

  if(type.id() == ID_bool)
  {
    if(vhdl_type == "boolean" || vhdl_type.empty())
      return src.is_true() ? "true" : "false";
    else // bit, std_logic
      return src.is_true() ? "'1'" : "'0'";
  }
  else if(type.id() == ID_unsignedbv || type.id() == ID_signedbv)
  {
    if(type.get(ID_C_vhdl_element).empty())
    {
      // an integer
      return integer2string(numeric_cast_v<mp_integer>(src));
    }
    else
    {
      // a vector, as a string of bits, most significant first
      auto width = to_bitvector_type(type).get_width();
      auto i = bvrep2integer(src.get_value(), width, false);
      return '"' + integer2binary(i, width) + '"';
    }
  }
  else if(type.id() == ID_integer || type.id() == ID_natural)
    return value;
  else if(type.id() == ID_char)
    return '\'' + value + '\'';
  else if(type.id() == ID_enumeration)
    return value;
  else
    return convert_norep(src, precedence);
}

/// IEEE 1076-2008 9.3.3: a positional aggregate
std::string
expr2vhdlt::convert_array(const array_exprt &src, unsigned precedence)
{
  std::string dest = "(";

  auto &element_type = to_array_type(src.type()).element_type();

  bool first = true;
  for(auto &element : src.operands())
  {
    if(first)
      first = false;
    else
      dest += ", ";

    // the values from the solver lack the VHDL type name
    exprt op = element;
    if(op.type() == element_type)
      op.type() = element_type;

    dest += convert(op);
  }

  return dest + ")";
}

/// IEEE 1076-2008 9.3.3: an aggregate with an others choice
std::string
expr2vhdlt::convert_array_of(const array_of_exprt &src, unsigned precedence)
{
  return "(others => " + convert(src.what()) + ")";
}

/// IEEE 1076-2008 9.3.3: a record value, as a named aggregate
std::string
expr2vhdlt::convert_struct(const struct_exprt &src, unsigned precedence)
{
  auto &components = to_struct_type(src.type()).components();

  if(components.size() != src.operands().size())
    return convert_norep(src, precedence);

  std::string dest = "(";

  for(std::size_t i = 0; i < components.size(); i++)
  {
    if(i != 0)
      dest += ", ";

    // the values from the solver lack the VHDL type name
    exprt op = src.operands()[i];
    if(op.type() == components[i].type())
      op.type() = components[i].type();

    dest += id2string(components[i].get_name()) + " => " + convert(op);
  }

  return dest + ")";
}

std::string expr2vhdlt::convert(const exprt &src, unsigned &precedence)
{
  precedence = PRECEDENCE_PRIMARY;
  auto id = src.id();

  // IEEE 1076-2008 9.2.6, 9.2.7: adding and multiplying operators
  if(id == ID_plus)
    return convert_binary(src, "+", precedence = PRECEDENCE_ADD);
  else if(id == ID_minus)
  {
    if(src.operands().size() < 2)
      return convert_norep(src, precedence);
    return convert_binary(src, "-", precedence = PRECEDENCE_ADD);
  }
  else if(id == ID_concatenation)
    return convert_concatenation(
      to_concatenation_expr(src), precedence = PRECEDENCE_ADD);
  else if(id == ID_mult)
    return convert_binary(src, "*", precedence = PRECEDENCE_MULT);
  else if(id == ID_div)
    return convert_binary(src, "/", precedence = PRECEDENCE_MULT);
  else if(id == ID_mod)
  {
    // CBMC's mod truncates towards zero, as VHDL's rem does
    return convert_binary(src, "rem", precedence = PRECEDENCE_MULT);
  }
  else if(id == ID_power)
    return convert_binary(src, "**", precedence = PRECEDENCE_MISC);
  else if(id == ID_abs)
    return convert_unary(
      to_unary_expr(src), "abs ", precedence = PRECEDENCE_MISC);
  else if(id == ID_unary_minus)
    return convert_unary(to_unary_expr(src), "-", precedence = PRECEDENCE_SIGN);
  else if(id == ID_unary_plus)
    return convert_unary(to_unary_expr(src), "+", precedence = PRECEDENCE_SIGN);

  // IEEE 1076-2008 9.2.4: shift operators
  else if(id == ID_shl)
    return convert_binary(src, "sll", precedence = PRECEDENCE_SHIFT);
  else if(id == ID_lshr)
    return convert_binary(src, "srl", precedence = PRECEDENCE_SHIFT);
  else if(id == ID_ashr)
    return convert_binary(src, "sra", precedence = PRECEDENCE_SHIFT);
  else if(id == ID_vhdl_sla)
    return convert_binary(src, "sla", precedence = PRECEDENCE_SHIFT);
  else if(id == ID_rol)
    return convert_binary(src, "rol", precedence = PRECEDENCE_SHIFT);
  else if(id == ID_ror)
    return convert_binary(src, "ror", precedence = PRECEDENCE_SHIFT);

  // IEEE 1076-2008 9.2.3: relational operators
  else if(id == ID_equal)
    return convert_binary(src, "=", precedence = PRECEDENCE_RELATION);
  else if(id == ID_notequal)
    return convert_binary(src, "/=", precedence = PRECEDENCE_RELATION);
  else if(id == ID_lt)
    return convert_binary(src, "<", precedence = PRECEDENCE_RELATION);
  else if(id == ID_le)
    return convert_binary(src, "<=", precedence = PRECEDENCE_RELATION);
  else if(id == ID_gt)
    return convert_binary(src, ">", precedence = PRECEDENCE_RELATION);
  else if(id == ID_ge)
    return convert_binary(src, ">=", precedence = PRECEDENCE_RELATION);

  // IEEE 1076-2008 9.2.2: logical operators, on booleans and vectors
  else if(id == ID_not || id == ID_bitnot)
    return convert_unary(
      to_unary_expr(src), "not ", precedence = PRECEDENCE_MISC);
  else if(id == ID_and || id == ID_bitand)
    return convert_logical(src, "and", precedence);
  else if(id == ID_or || id == ID_bitor)
    return convert_logical(src, "or", precedence);
  else if(id == ID_xor || id == ID_bitxor)
    return convert_logical(src, "xor", precedence);
  else if(id == ID_nand || id == ID_bitnand)
    return convert_logical(src, "nand", precedence);
  else if(id == ID_nor || id == ID_bitnor)
    return convert_logical(src, "nor", precedence);
  else if(id == ID_xnor || id == ID_bitxnor)
    return convert_logical(src, "xnor", precedence);

  // PSL
  else if(id == ID_implies)
    return convert_binary(src, "->", precedence = PRECEDENCE_IMPLIES);
  else if(id == "<=>")
    return convert_binary(src, "<->", precedence = PRECEDENCE_IFF);
  else if(id == ID_G || id == ID_AG)
    return convert_unary(
      to_unary_expr(src), "always ", precedence = PRECEDENCE_TEMPORAL);
  else if(id == ID_F || id == ID_AF)
    return convert_unary(
      to_unary_expr(src), "eventually! ", precedence = PRECEDENCE_TEMPORAL);
  else if(id == ID_X || id == ID_AX)
    return convert_unary(
      to_unary_expr(src), "next ", precedence = PRECEDENCE_TEMPORAL);
  else if(id == ID_U || id == ID_AU)
    return convert_binary(src, "until", precedence = PRECEDENCE_TEMPORAL);
  else if(id == ID_EG || id == ID_EF || id == ID_EX)
    return convert_unary(
      to_unary_expr(src),
      id2string(id) + " ",
      precedence = PRECEDENCE_TEMPORAL);

  // the clock edge expressions of the type checker
  else if(id == ID_vhdl_event)
    return convert_operand(to_unary_expr(src).op(), PRECEDENCE_PRIMARY) +
           "'event";
  else if(id == ID_vhdl_rising_edge)
    return "rising_edge(" + convert(to_unary_expr(src).op()) + ")";
  else if(id == ID_vhdl_falling_edge)
    return "falling_edge(" + convert(to_unary_expr(src).op()) + ")";

  // names and values
  else if(id == ID_if)
    return convert_if(to_if_expr(src));
  else if(id == ID_with)
    return convert_with(to_with_expr(src), precedence);
  else if(id == ID_update_bit)
    return convert_update_bit(to_update_bit_expr(src), precedence);
  else if(id == ID_replication)
    return convert_replication(to_replication_expr(src), precedence);
  else if(id == ID_array)
    return convert_array(to_array_expr(src), precedence);
  else if(id == ID_array_of)
    return convert_array_of(to_array_of_expr(src), precedence);
  else if(id == ID_struct)
    return convert_struct(to_struct_expr(src), precedence);
  else if(id == ID_index)
    return convert_index(to_index_expr(src), precedence);
  else if(id == ID_extractbit)
    return convert_extractbit(to_extractbit_expr(src), precedence);
  else if(id == ID_extractbits)
    return convert_extractbits(to_extractbits_expr(src), precedence);
  else if(id == ID_member)
    return convert_member(to_member_expr(src), precedence);
  else if(id == ID_typecast)
    return convert_typecast(to_typecast_expr(src), precedence);
  else if(id == ID_symbol)
    return convert_symbol(to_symbol_expr(src), precedence);
  else if(id == ID_nondet_symbol)
    return convert_nondet_symbol(src, precedence);
  else if(id == ID_next_symbol)
    return convert_next_symbol(src, precedence);
  else if(id == ID_constant)
    return convert_constant(to_constant_expr(src), precedence);

  // no VHDL representation
  return convert_norep(src, precedence);
}

std::string expr2vhdlt::convert(const exprt &src)
{
  unsigned precedence;
  return convert(src, precedence);
}

/// the VHDL type name, with the index range for arrays, when recorded
/// on the CBMC type; otherwise a description of the CBMC type
std::string expr2vhdlt::convert(const typet &type)
{
  auto vhdl_type = type.get(ID_C_vhdl_type);
  auto direction = type.get(ID_C_vhdl_direction);

  std::string range;
  if(!direction.empty())
    range = "(" + type.get_string(ID_C_vhdl_left) +
            (direction == ID_vhdl_downto ? " downto " : " to ") +
            type.get_string(ID_C_vhdl_right) + ")";

  if(!vhdl_type.empty())
    return id2string(vhdl_type) + range;

  if(type.id() == ID_bool)
    return "boolean";
  else if(type.id() == ID_unsignedbv || type.id() == ID_signedbv)
  {
    auto width = to_bitvector_type(type).get_width();
    if(!range.empty())
      return (type.id() == ID_signedbv ? "signed" : "bit_vector") + range;
    return std::string(type.id() == ID_signedbv ? "signed" : "bit_vector") +
           "(" + std::to_string(width == 0 ? 0 : width - 1) + " downto 0)";
  }
  else if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    return "array (0 to " +
           integer2string(
             numeric_cast_v<mp_integer>(to_constant_expr(array_type.size())) -
             1) +
           ") of " + convert(array_type.element_type());
  }
  else if(type.id() == ID_struct)
  {
    std::string dest = "record ";
    for(auto &c : to_struct_type(type).components())
      dest += id2string(c.get_name()) + " : " + convert(c.type()) + "; ";
    return dest + "end record";
  }
  else if(type.id() == ID_enumeration)
  {
    std::string dest = "(";
    bool first = true;
    for(auto &e : to_enumeration_type(type).elements())
    {
      if(first)
        first = false;
      else
        dest += ", ";
      dest += id2string(e.id());
    }
    return dest + ")";
  }
  else if(type.id() == ID_integer)
    return "integer";
  else if(type.id() == ID_real)
    return "real";

  return id2string(type.id());
}

std::string expr2vhdl(const exprt &expr)
{
  expr2vhdlt expr2vhdl;
  return expr2vhdl.convert(expr);
}

std::string type2vhdl(const typet &type)
{
  expr2vhdlt expr2vhdl;
  return expr2vhdl.convert(type);
}
