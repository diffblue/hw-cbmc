/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr2verilog.h"
#include "expr2verilog_class.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/lispexpr.h>
#include <util/lispirep.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "sva_expr.h"
#include "verilog_expr.h"
#include "verilog_types.h"

#include <algorithm>
#include <cstdlib>
#include <sstream>

/*******************************************************************\

Function: expr2verilogt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_if(const if_exprt &src, verilog_precedencet precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest;

  auto op0 = convert_rec(src.op0());
  auto op1 = convert_rec(src.op1());
  auto op2 = convert_rec(src.op2());

  if(precedence > op0.p)
    dest += '(';
  dest += op0.s;
  if(precedence > op0.p)
    dest += ')';

  dest+=" ? ";

  if(precedence > op0.p)
    dest += '(';
  dest += op1.s;
  if(precedence > op0.p)
    dest += ')';

  dest+=" : ";

  if(precedence > op0.p)
    dest += '(';
  dest += op2.s;
  if(precedence > op0.p)
    dest += ')';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_cycle_delay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_cycle_delay(
  const ternary_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=3)
    return convert_norep(src, precedence);

  std::string dest="##";

  auto op0 = convert_rec(src.op0());
  auto op1 = convert_rec(src.op1());
  auto op2 = convert_rec(src.op2());

  if(src.op1().is_nil())
    dest += op0.s;
  else if(src.op1().id()==ID_infinity)
    dest += '[' + op0.s + ':' + '$' + ']';
  else
    dest += '[' + op0.s + ':' + op1.s + ']';

  dest+=' ';

  if(precedence > op2.p)
    dest += '(';
  dest += op2.s;
  if(precedence > op2.p)
    dest += ')';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_sequence_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_sequence_concatenation(
  const binary_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest;

  auto op0 = convert_rec(src.op0());
  auto op1 = convert_rec(src.op1());

  if(precedence > op0.p)
    dest += '(';
  dest += op0.s;
  if(precedence > op0.p)
    dest += ')';

  dest+=' ';

  if(precedence > op0.p)
    dest += '(';
  dest += op1.s;
  if(precedence > op0.p)
    dest += ')';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_binary(
  const multi_ary_exprt &src,
  const std::string &symbol,
  verilog_precedencet precedence)
{
  if(src.operands().size()<2)
    return convert_norep(src, precedence);

  bool first=true;
  std::string dest;

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
    {
      dest+=' ';
      dest+=symbol;
      dest+=' ';
    }

    auto op = convert_rec(*it);

    if(precedence > op.p)
      dest += '(';
    dest += op.s;
    if(precedence > op.p)
      dest += ')';
  }

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_with(
  const with_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()<1)
    return convert_norep(src, precedence);

  std::string dest = "(" + convert_rec(src.old()).s;

  for(unsigned i=1; i<src.operands().size(); i+=2)
  {
    dest+=" WITH ";
    dest += convert_rec(src.operands()[i]).s;
    dest+=":=";
    dest += convert_rec(src.operands()[i + 1]).s;
  }

  dest+=")";

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_concatenation(
  const concatenation_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()<1)
    return convert_norep(src, precedence);

  bool first=true;
  std::string dest="{ ";

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    auto op = convert_rec(*it);

    if(precedence > op.p)
      dest += '(';
    dest += op.s;
    if(precedence > op.p)
      dest += ')';
  }

  dest+=" }";

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_function(const std::string &name, const exprt &src)
{
  bool first=true;
  std::string dest=name;
  dest+="(";

  forall_operands(it, src)
  {
    if(first)
      first=false;
    else
      dest+=", ";

    dest += convert_rec(*it).s;
  }

  dest+=")";

  return {verilog_precedencet::MIN, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_function_call(const function_call_exprt &src)
{
  if(src.operands().size()!=2)
  {
    verilog_precedencet p;
    return convert_norep(src, p);
  }

  auto fkt = convert_rec(src.op0());

  std::string dest = fkt.s;
  bool first=true;
  dest+="(";

  for(const auto & op : src.op1().operands())
  {
    if(first)
      first=false;
    else
      dest+=", ";

    dest += convert_rec(op).s;
  }

  dest+=")";

  return {verilog_precedencet::MIN, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_ranged_predicate(
  const std::string &name,
  const sva_ranged_predicate_exprt &src)
{
  std::string range_str;

  range_str = "[" + convert(src.lower()) + ':';
  if(src.upper().id() == ID_infinity)
    range_str += "$";
  else
    range_str += convert(src.upper());
  range_str += "] ";

  auto &src_op = src.op();
  auto op = convert_rec(src_op);
  if(op.p == verilog_precedencet::MIN && src_op.operands().size() >= 2)
    op.s = "(" + op.s + ")";

  return {verilog_precedencet::MIN, name + " " + range_str + op.s};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_sva_case(const sva_case_exprt &src)
{
  std::string cases;

  for(auto &case_item : src.case_items())
  {
    bool first = true;
    for(auto &pattern : case_item.patterns())
    {
      if(first)
        first = false;
      else
        cases += ", ";
      cases += convert(pattern);
    }

    cases += ": ";
    cases += convert(case_item.result());
    cases += "; ";
  }

  return {
    verilog_precedencet::MIN,
    "case(" + convert(src.case_op()) + ") " + cases + "endcase"};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_unary(
  const std::string &name,
  const unary_exprt &src)
{
  auto op = convert_rec(src.op());
  if(op.p == verilog_precedencet::MIN && src.op().operands().size() >= 2)
    op.s = "(" + op.s + ")";
  return {verilog_precedencet::MIN, name + " " + op.s};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_binary(
  const std::string &name,
  const binary_exprt &expr)
{
  auto op0 = convert_rec(expr.lhs());
  if(op0.p == verilog_precedencet::MIN)
    op0.s = "(" + op0.s + ")";

  auto op1 = convert_rec(expr.rhs());
  if(op1.p == verilog_precedencet::MIN)
    op1.s = "(" + op1.s + ")";

  return {verilog_precedencet::MIN, op0.s + " " + name + " " + op1.s};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_abort

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_abort(
  const std::string &text,
  const sva_abort_exprt &expr)
{
  auto op0 = convert_rec(expr.condition());
  auto op1 = convert_rec(expr.property());

  return {verilog_precedencet::MIN, text + " (" + op0.s + ") " + op1.s};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_indexed_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_indexed_binary(
  const std::string &name,
  const binary_exprt &expr)
{
  std::string op0;

  if(expr.op0().is_not_nil())
    op0 = '[' + convert_rec(expr.lhs()).s + ']';

  auto op1 = convert_rec(expr.rhs());
  if(op1.p == verilog_precedencet::MIN)
    op1.s = "(" + op1.s + ")";

  return {verilog_precedencet::MIN, name + op0 + ' ' + op1.s};
}

/*******************************************************************\

Function: expr2verilogt::convert_sva_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_sva_if(const sva_if_exprt &src)
{
  if(src.false_case().is_nil())
    return {
      verilog_precedencet::MIN,
      "if(" + convert_rec(src.cond()).s + ") " +
        convert_rec(src.true_case()).s};
  else
    return {
      verilog_precedencet::MIN,
      "if(" + convert_rec(src.cond()).s + ") " +
        convert_rec(src.true_case()).s + " else " +
        convert_rec(src.false_case()).s};
}

/*******************************************************************\

Function: expr2verilogt::convert_replication

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_replication(
  const replication_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  std::string dest="{ ";

  dest += convert_rec(src.op0()).s;
  dest+=" { ";
  dest += convert_rec(src.op1()).s;
  dest+=" } }";

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_unary(
  const unary_exprt &src,
  const std::string &symbol,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  auto op = convert_rec(src.op());

  std::string dest=symbol;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_typecast(
  const typecast_exprt &src,
  verilog_precedencet &precedence)
{
  if(src.operands().size()==1)
  {
    //const typet &from=src.op0().type();
    //const typet &to=src.type();

    // just ignore them for now
    return {precedence, convert_rec(src.op()).s};
  }

  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2verilogt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_index(
  const index_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  auto op = convert_rec(src.op0());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  dest+='[';
  dest += convert_rec(src.op1()).s;
  dest+=']';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_non_indexed_part_select

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_non_indexed_part_select(
  const verilog_non_indexed_part_select_exprt &src,
  verilog_precedencet precedence)
{
  auto op = convert_rec(src.src());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  dest += '[';
  dest += convert_rec(src.msb()).s;
  dest += ':';
  dest += convert_rec(src.lsb()).s;
  dest += ']';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_indexed_part_select

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_indexed_part_select(
  const verilog_indexed_part_select_plus_or_minus_exprt &src,
  verilog_precedencet precedence)
{
  auto op = convert_rec(src.src());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  dest += '[';
  dest += convert_rec(src.index()).s;

  if(src.id() == ID_verilog_indexed_part_select_plus)
    dest += '+';
  else
    dest += '-';

  dest += convert_rec(src.width()).s;
  dest += ']';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_extractbit(
  const extractbit_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=2)
    return convert_norep(src, precedence);

  auto op = convert_rec(src.op0());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  dest+='[';
  dest += convert_rec(src.op1()).s;
  dest+=']';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_extractbits(
  const extractbits_exprt &src,
  verilog_precedencet precedence)
{
  auto op = convert_rec(src.src());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  auto width = to_bitvector_type(src.type()).get_width();

  dest+='[';

  if(src.index().is_constant())
  {
    auto index_int = numeric_cast_v<mp_integer>(to_constant_expr(src.index()));
    dest += integer2string(index_int + width);
  }
  else
  {
    dest += convert_rec(src.index()).s;
    dest += " + ";
    dest += std::to_string(width);
  }

  dest+=':';
  dest += convert_rec(src.index()).s;
  dest+=']';

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_member(
  const member_exprt &src,
  verilog_precedencet precedence)
{
  if(src.operands().size()!=1)
    return convert_norep(src, precedence);

  auto op = convert_rec(src.compound());

  std::string dest;
  if(precedence > op.p)
    dest += '(';
  dest += op.s;
  if(precedence > op.p)
    dest += ')';

  dest+='.';
  dest += id2string(src.get_component_name());

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_norep

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_norep(const exprt &src, verilog_precedencet &precedence)
{
  precedence = verilog_precedencet::MAX;
  return {precedence, src.pretty()};
}

/*******************************************************************\

Function: expr2verilogt::convert_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_symbol(const exprt &src, verilog_precedencet &precedence)
{
  precedence = verilog_precedencet::MAX;
  std::string dest=src.get_string(ID_identifier);
 
  if(std::string(dest, 0, 9)=="Verilog::")
    dest.erase(0, 9);

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_nondet_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_nondet_symbol(
  const exprt &src,
  verilog_precedencet &precedence)
{
  return {precedence, "nondet(" + convert_symbol(src, precedence).s + ")"};
}

/*******************************************************************\

Function: expr2verilogt::convert_next_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_next_symbol(
  const exprt &src,
  verilog_precedencet &precedence)
{
  return {precedence, "next(" + convert_symbol(src, precedence).s + ")"};
}

/*******************************************************************\

Function: expr2verilogt::convert_hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_hierarchical_identifier(
  const hierarchical_identifier_exprt &src,
  verilog_precedencet &precedence)
{
  precedence = verilog_precedencet::MAX;
  return {
    precedence,
    convert_rec(src.module()).s + '.' + src.item().get_string(ID_base_name)};
}

/*******************************************************************\

Function: expr2verilogt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_constant(
  const constant_exprt &src,
  verilog_precedencet &precedence)
{
  precedence = verilog_precedencet::MAX;

  const typet &type=src.type();
  std::string dest;

  if(type.get(ID_C_verilog_type) == ID_verilog_enum)
  {
    // Get the numerical value.
    auto int_value = numeric_cast_v<mp_integer>(src);

    // Look up the enum type symbol.
    auto enum_type_identifier = type.get(ID_C_identifier);
    auto &symbol = ns.lookup(enum_type_identifier);
    auto &enum_type = to_verilog_enum_type(symbol.type);

    // Find the enum name with the matching value.
    for(auto &enum_name : enum_type.enum_names())
    {
      auto &enum_symbol = ns.lookup(enum_name.identifier());
      DATA_INVARIANT(
        enum_symbol.value.id() == ID_constant,
        "enum name value must be constant");
      auto enum_int_value =
        numeric_cast_v<mp_integer>(to_constant_expr(enum_symbol.value));
      if(enum_int_value == int_value)
        return {precedence, id2string(enum_symbol.display_name())};
    }

    return {precedence, integer2string(int_value)};
  }
  else if(type.id() == ID_bool)
  {
    if(src.is_true())
      dest+='1';
    else
      dest+='0';
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv)
  {
    auto width = to_bitvector_type(type).get_width();
    auto i = numeric_cast_v<mp_integer>(src);

    if(i>=256)
    {
      dest = std::to_string(width);
      dest += "'h";
      if(type.id() == ID_signedbv)
        dest += 's';
      dest += integer2string(i, 16);
    }
    else if(width<=7)
    {
      dest=std::to_string(width);
      dest+="'";
      if(type.id()==ID_signedbv) dest+='s';
      dest+='b';
      dest += integer2binary(i, width);
    }
    else
      dest=integer2string(i);
  }
  else if(type.id()==ID_verilog_signedbv)
  {
    // these have a binary representation
    const irep_idt &value = src.get_value();
    unsigned width=to_verilog_signedbv_type(src.type()).get_width();
    return {precedence, std::to_string(width) + "'sb" + id2string(value)};
  }
  else if(type.id()==ID_verilog_unsignedbv)
  {
    // these have a binary representation
    const irep_idt &value = src.get_value();
    unsigned width=to_verilog_unsignedbv_type(src.type()).get_width();
    return {precedence, std::to_string(width) + "'b" + id2string(value)};
  }
  else if(type.id()==ID_integer || type.id()==ID_natural ||
          type.id()==ID_range)
  {
    // these have a decimal representation
    const irep_idt &value = src.get_value();
    dest=id2string(value);
  }
  else
    return convert_norep(src, precedence);

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt
expr2verilogt::convert_array(const exprt &src, verilog_precedencet precedence)
{
  std::string dest="{ ";

  forall_operands(it, src)
  {
    auto tmp = convert_rec(*it).s;

    exprt::operandst::const_iterator next_it=it;
    next_it++;

    if(next_it!=src.operands().end())
    {
      tmp+=", ";
      if(tmp.size()>40) tmp+="\n    ";
    }

    dest+=tmp;
  }

  dest+=" }";

  return {precedence, dest};
}

/*******************************************************************\

Function: expr2verilogt::convert_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

expr2verilogt::resultt expr2verilogt::convert_rec(const exprt &src)
{
  verilog_precedencet precedence = verilog_precedencet::MAX;

  if(src.id()==ID_plus)
    return convert_binary(
      to_multi_ary_expr(src), "+", precedence = verilog_precedencet::ADD);

  else if(src.id()==ID_if)
    return convert_if(to_if_expr(src), precedence = verilog_precedencet::IF);

  else if(src.id()==ID_concatenation)
    return convert_concatenation(
      to_concatenation_expr(src), precedence = verilog_precedencet::CONCAT);

  else if(src.id()==ID_with)
    return convert_with(to_with_expr(src), precedence);

  else if(src.id()==ID_replication)
    return convert_replication(
      to_replication_expr(src), precedence = verilog_precedencet::CONCAT);

  else if(src.id()==ID_array)
    return convert_array(src, precedence);

  else if(src.id()==ID_minus)
  {
    if(src.operands().size()!=2)
      return convert_norep(src, precedence);
    else
      return convert_binary(
        to_multi_ary_expr(src), "-", precedence = verilog_precedencet::ADD);
  }

  else if(src.id()==ID_shl)
    return convert_binary(
      to_multi_ary_expr(src), "<<", precedence = verilog_precedencet::SHIFT);

  else if(src.id()==ID_lshr)
    return convert_binary(
      to_multi_ary_expr(src), ">>", precedence = verilog_precedencet::SHIFT);

  else if(src.id()==ID_ashr)
    return convert_binary(
      to_multi_ary_expr(src), ">>>", precedence = verilog_precedencet::SHIFT);

  else if(src.id()==ID_unary_minus)
    return convert_unary(
      to_unary_minus_expr(src), "-", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_unary_plus)
    return convert_unary(
      to_unary_plus_expr(src), "+", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_index)
    return convert_index(
      to_index_expr(src), precedence = verilog_precedencet::MEMBER);

  else if(
    src.id() == ID_verilog_indexed_part_select_plus ||
    src.id() == ID_verilog_indexed_part_select_minus)
  {
    return convert_indexed_part_select(
      to_verilog_indexed_part_select_plus_or_minus_expr(src),
      precedence = verilog_precedencet::MEMBER);
  }

  else if(src.id() == ID_verilog_non_indexed_part_select)
    return convert_non_indexed_part_select(
      to_verilog_non_indexed_part_select_expr(src),
      precedence = verilog_precedencet::MEMBER);

  else if(src.id()==ID_extractbit)
    return convert_extractbit(
      to_extractbit_expr(src), precedence = verilog_precedencet::MEMBER);

  else if(src.id()==ID_extractbits)
    return convert_extractbits(
      to_extractbits_expr(src), precedence = verilog_precedencet::MEMBER);

  else if(src.id()==ID_member)
    return convert_member(
      to_member_expr(src), precedence = verilog_precedencet::MEMBER);

  else if(src.id()==ID_mult)
    return convert_binary(
      to_multi_ary_expr(src), "*", precedence = verilog_precedencet::MULT);

  else if(src.id()==ID_div)
    return convert_binary(
      to_multi_ary_expr(src), "/", precedence = verilog_precedencet::MULT);

  else if(src.id()==ID_lt)
    return convert_binary(
      to_multi_ary_expr(src), "<", precedence = verilog_precedencet::RELATION);

  else if(src.id()==ID_gt)
    return convert_binary(
      to_multi_ary_expr(src), ">", precedence = verilog_precedencet::RELATION);

  else if(src.id()==ID_le)
    return convert_binary(
      to_multi_ary_expr(src), "<=", precedence = verilog_precedencet::RELATION);

  else if(src.id()==ID_ge)
    return convert_binary(
      to_multi_ary_expr(src), ">=", precedence = verilog_precedencet::RELATION);

  else if(src.id()==ID_equal)
    return convert_binary(
      to_multi_ary_expr(src), "==", precedence = verilog_precedencet::EQUALITY);

  else if(src.id() == ID_verilog_logical_equality)
    return convert_binary(
      to_multi_ary_expr(src), "==", precedence = verilog_precedencet::EQUALITY);

  else if(src.id()==ID_notequal)
    return convert_binary(
      to_multi_ary_expr(src), "!=", precedence = verilog_precedencet::EQUALITY);

  else if(src.id() == ID_verilog_logical_inequality)
    return convert_binary(
      to_multi_ary_expr(src), "!=", precedence = verilog_precedencet::EQUALITY);

  else if(src.id()==ID_verilog_case_equality)
    return convert_binary(
      to_multi_ary_expr(src),
      "===",
      precedence = verilog_precedencet::EQUALITY);

  else if(src.id()==ID_verilog_case_inequality)
    return convert_binary(
      to_multi_ary_expr(src),
      "!==",
      precedence = verilog_precedencet::EQUALITY);

  else if(src.id() == ID_verilog_wildcard_equality)
    return convert_binary(
      to_multi_ary_expr(src),
      "==?",
      precedence = verilog_precedencet::EQUALITY);

  else if(src.id() == ID_verilog_wildcard_inequality)
    return convert_binary(
      to_multi_ary_expr(src),
      "!=?",
      precedence = verilog_precedencet::EQUALITY);

  else if(src.id()==ID_not)
    return convert_unary(
      to_not_expr(src), "!", precedence = verilog_precedencet::NOT);

  else if(src.id() == ID_sva_not)
    return convert_sva_unary("not", to_sva_not_expr(src));

  else if(src.id()==ID_bitnot)
    return convert_unary(
      to_bitnot_expr(src), "~", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_typecast)
    return convert_typecast(to_typecast_expr(src), precedence);

  else if(src.id()==ID_and)
    return convert_binary(
      to_multi_ary_expr(src), "&&", precedence = verilog_precedencet::AND);

  else if(src.id() == ID_sva_and)
    return convert_sva_binary("and", to_sva_and_expr(src));

  else if(src.id() == ID_sva_iff)
    return convert_sva_binary("iff", to_sva_iff_expr(src));

  else if(src.id() == ID_sva_implies)
    return convert_sva_binary("implies", to_sva_implies_expr(src));

  else if(src.id()==ID_power)
    return convert_binary(
      to_multi_ary_expr(src), "**", precedence = verilog_precedencet::POWER);

  else if(src.id()==ID_bitand)
    return convert_binary(
      to_multi_ary_expr(src), "&", precedence = verilog_precedencet::BITAND);

  else if(src.id()==ID_bitxor)
    return convert_binary(
      to_multi_ary_expr(src), "^", precedence = verilog_precedencet::XOR);

  else if(src.id()==ID_bitxnor)
    return convert_binary(
      to_multi_ary_expr(src), "~^", precedence = verilog_precedencet::XOR);

  else if(src.id()==ID_mod)
    return convert_binary(
      to_multi_ary_expr(src), "%", precedence = verilog_precedencet::MULT);

  else if(src.id()==ID_or)
    return convert_binary(
      to_multi_ary_expr(src), "||", precedence = verilog_precedencet::OR);

  else if(src.id() == ID_sva_or)
    return convert_sva_binary("or", to_sva_or_expr(src));

  else if(src.id()==ID_bitor)
    return convert_binary(
      to_multi_ary_expr(src), "|", precedence = verilog_precedencet::BITOR);

  else if(src.id()==ID_implies)
    return convert_binary(
      to_multi_ary_expr(src), "->", precedence = verilog_precedencet::IMPLIES);

  else if(src.id()==ID_iff)
    return convert_binary(
      to_multi_ary_expr(src), "<->", precedence = verilog_precedencet::IMPLIES);

  else if(src.id()==ID_reduction_or)
    return convert_unary(
      to_unary_expr(src), "|", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_reduction_and)
    return convert_unary(
      to_unary_expr(src), "&", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_reduction_nor)
    return convert_unary(
      to_unary_expr(src), "~|", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_reduction_nand)
    return convert_unary(
      to_unary_expr(src), "~&", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_reduction_xor)
    return convert_unary(
      to_unary_expr(src), "^", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_reduction_xnor)
    return convert_unary(
      to_unary_expr(src), "~^", precedence = verilog_precedencet::NOT);

  else if(src.id()==ID_AG || src.id()==ID_EG ||
          src.id()==ID_AX || src.id()==ID_EX)
    return convert_unary(
      to_unary_expr(src),
      src.id_string() + " ",
      precedence = verilog_precedencet::MIN);

  else if(src.id()==ID_symbol)
    return convert_symbol(src, precedence);

  else if(src.id()==ID_nondet_symbol)
    return convert_nondet_symbol(src, precedence);

  else if(src.id()==ID_next_symbol)
    return convert_next_symbol(src, precedence);

  else if(src.id() == ID_hierarchical_identifier)
    return convert_hierarchical_identifier(
      to_hierarchical_identifier_expr(src), precedence);

  else if(src.id()==ID_constant)
    return convert_constant(to_constant_expr(src), precedence);
    
  else if(src.id()==ID_constraint_select_one)
    return convert_function("$ND", src);

  else if(src.id() == ID_verilog_past)
    return convert_function("$past", src);

  else if(src.id()==ID_onehot)
    return convert_function("$onehot", src);
    
  else if(src.id()==ID_onehot0)
    return convert_function("$onehot0", src);

  else if(src.id()==ID_sva_overlapped_implication)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("|->", to_binary_expr(src));

  else if(src.id()==ID_sva_non_overlapped_implication)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("|=>", to_binary_expr(src));

  else if(src.id() == ID_sva_cycle_delay_star)
    return convert_sva_unary("##[*]", to_unary_expr(src));

  else if(src.id() == ID_sva_cycle_delay_plus)
    return convert_sva_unary("##[+]", to_unary_expr(src));

  else if(src.id() == ID_sva_overlapped_followed_by)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("#-#", to_binary_expr(src));

  else if(src.id() == ID_sva_nonoverlapped_followed_by)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("#=#", to_binary_expr(src));

  else if(src.id()==ID_sva_cycle_delay)
    return convert_sva_cycle_delay(
      to_ternary_expr(src), precedence = verilog_precedencet::MIN);
    // not sure about precedence

  else if(src.id() == ID_sva_strong)
    return convert_function("strong", src);

  else if(src.id() == ID_sva_weak)
    return convert_function("weak", src);

  else if(src.id()==ID_sva_sequence_concatenation)
    return convert_sva_sequence_concatenation(
      to_binary_expr(src), precedence = verilog_precedencet::MIN);
    // not sure about precedence

  else if(src.id() == ID_sva_sequence_first_match)
    return convert_function("first_match", src);

  else if(src.id() == ID_sva_sequence_intersect)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("intersect", to_binary_expr(src));
  // not sure about precedence

  else if(src.id() == ID_sva_sequence_within)
    return convert_sva_sequence_concatenation(
      to_binary_expr(src), precedence = verilog_precedencet::MIN);
  // not sure about precedence

  else if(src.id() == ID_sva_sequence_throughout)
    return convert_sva_sequence_concatenation(
      to_binary_expr(src), precedence = verilog_precedencet::MIN);
  // not sure about precedence

  else if(src.id()==ID_sva_always)
    return precedence = verilog_precedencet::MIN,
           convert_sva_unary("always", to_sva_always_expr(src));

  else if(src.id() == ID_sva_ranged_always)
  {
    return precedence = verilog_precedencet::MIN,
           convert_sva_ranged_predicate(
             "always", to_sva_ranged_always_expr(src));
  }

  else if(src.id() == ID_sva_s_always)
  {
    return precedence = verilog_precedencet::MIN,
           convert_sva_ranged_predicate("s_always", to_sva_s_always_expr(src));
  }

  else if(src.id() == ID_sva_cover)
    return precedence = verilog_precedencet::MIN,
           convert_sva_unary("cover", to_sva_cover_expr(src));

  else if(src.id() == ID_sva_assume)
    return precedence = verilog_precedencet::MIN,
           convert_sva_unary("assume", to_sva_assume_expr(src));

  else if(src.id() == ID_sva_accept_on)
    return precedence = verilog_precedencet::MIN,
           convert_sva_abort("accept_on", to_sva_abort_expr(src));

  else if(src.id() == ID_sva_reject_on)
    return precedence = verilog_precedencet::MIN,
           convert_sva_abort("reject_on", to_sva_abort_expr(src));

  else if(src.id() == ID_sva_sync_accept_on)
    return precedence = verilog_precedencet::MIN,
           convert_sva_abort("sync_accept_on", to_sva_abort_expr(src));

  else if(src.id() == ID_sva_sync_reject_on)
    return precedence = verilog_precedencet::MIN,
           convert_sva_abort("sync_reject_on", to_sva_abort_expr(src));

  else if(src.id()==ID_sva_nexttime)
    return precedence = verilog_precedencet::MIN,
           convert_sva_indexed_binary("nexttime", to_sva_nexttime_expr(src));

  else if(src.id() == ID_sva_disable_iff)
    return precedence = verilog_precedencet::MIN,
           convert_sva_abort("disable iff", to_sva_abort_expr(src));

  else if(src.id()==ID_sva_s_nexttime)
    return precedence = verilog_precedencet::MIN,
           convert_sva_indexed_binary(
             "s_nexttime", to_sva_s_nexttime_expr(src));

  else if(src.id()==ID_sva_eventually)
  {
    return precedence = verilog_precedencet::MIN,
           convert_sva_ranged_predicate(
             "eventually", to_sva_eventually_expr(src));
  }

  else if(src.id()==ID_sva_s_eventually)
    return precedence = verilog_precedencet::MIN,
           convert_sva_unary("s_eventually", to_sva_s_eventually_expr(src));

  else if(src.id() == ID_sva_ranged_s_eventually)
    return precedence = verilog_precedencet::MIN,
           convert_sva_ranged_predicate(
             "s_eventually", to_sva_ranged_s_eventually_expr(src));

  else if(src.id()==ID_sva_until)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("until", to_sva_until_expr(src));

  else if(src.id()==ID_sva_s_until)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("s_until", to_sva_s_until_expr(src));

  else if(src.id()==ID_sva_until_with)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("until_with", to_sva_until_with_expr(src));

  else if(src.id()==ID_sva_s_until_with)
    return precedence = verilog_precedencet::MIN,
           convert_sva_binary("s_until_with", to_sva_s_until_with_expr(src));

  else if(src.id() == ID_sva_if)
    return precedence = verilog_precedencet::MIN,
           convert_sva_if(to_sva_if_expr(src));

  else if(src.id() == ID_sva_case)
    return precedence = verilog_precedencet::MIN,
           convert_sva_case(to_sva_case_expr(src));

  else if(src.id()==ID_function_call)
    return convert_function_call(to_function_call_expr(src));

  else if(src.id() == ID_clog2)
    return convert_function("$clog2", src);

  // no VERILOG language expression for internal representation 
  return convert_norep(src, precedence);
}

/*******************************************************************\

Function: expr2verilogt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert(const exprt &src)
{
  return convert_rec(src).s;
}

/*******************************************************************\

Function: expr2verilogt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilogt::convert(const typet &type)
{
  if(type.id() == ID_verilog_shortint)
    return "shortint";
  else if(type.id() == ID_verilog_int)
    return "int";
  else if(type.id() == ID_verilog_longint)
    return "longint";
  else if(type.id() == ID_verilog_byte)
    return "byte";
  else if(type.id() == ID_verilog_bit)
    return "bit";
  else if(type.id() == ID_verilog_logic)
    return "logic";
  else if(type.id() == ID_verilog_integer)
    return "integer";
  else if(type.id() == ID_verilog_reg)
    return "reg";
  else if(type.id() == ID_verilog_time)
    return "time";
  else if(type.id() == ID_bool)
    return "bool";
  else if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
  {
    unsigned width=to_bitvector_type(type).get_width();
    bool big_endian = type.get_bool(ID_C_big_endian);
    unsigned offset=atoi(type.get(ID_C_offset).c_str());

    if(width!=0)
    {
      std::string dest;
      if(type.id()==ID_unsignedbv)
        dest="";
      else if(type.id()==ID_signedbv)
        dest="signed ";

      dest+='[';

      if(big_endian)
      {
        dest+=std::to_string(offset);
        dest += ":";
        dest += std::to_string(offset + width - 1);
      }
      else
      {
        dest+=std::to_string(offset+width-1);
        dest += ":";
        dest += std::to_string(offset);
      }

      dest+="]";
      return dest;
    }
  }
  else if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    std::string dest="array [";

    dest += convert(array_type.size());

    dest+="] of ";
    dest += convert(array_type.element_type());

    return dest;
  }
  else if(type.id() == ID_verilog_genvar)
    return "genvar";
  else if(type.id()==ID_integer)
    return "integer";
  else if(type.id()==ID_verilog_shortreal)
    return "shortreal";
  else if(type.id()==ID_verilog_real)
    return "real";
  else if(type.id()==ID_verilog_realtime)
    return "realtime";
  else if(type.id() == ID_verilog_enum)
  {
    return "enum";
  }
  else if(type.id() == ID_struct)
  {
    return "struct";
  }
  else if(type.id() == ID_union)
  {
    return "union";
  }
  else if(type.id() == ID_verilog_type_reference)
  {
    auto &type_reference = to_verilog_type_reference(type);
    if(type_reference.expression_op().is_not_nil())
      return "type(" + convert(type_reference.expression_op()) + ")";
    else
      return "type(" + convert(type_reference.type_op()) + ")";
  }

  return "IREP("+type.pretty()+")";
}

/*******************************************************************\

Function: expr2verilog

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2verilog(const exprt &expr, const namespacet &ns)
{
  expr2verilogt expr2verilog(ns);
  return expr2verilog.convert(expr);
}

/*******************************************************************\

Function: type2verilog

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2verilog(const typet &type, const namespacet &ns)
{
  expr2verilogt expr2verilog(ns);
  return expr2verilog.convert(type);
}
