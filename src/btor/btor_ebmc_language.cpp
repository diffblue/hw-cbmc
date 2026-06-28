/*******************************************************************\

Module: BTOR2 Language Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// BTOR2 Language Interface

#include "btor_ebmc_language.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/cmdline.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/transition_system.h>
#include <temporal-logic/ltl.h>
#include <trans-word-level/next_symbol.h>
#include <verilog/verilog_expr.h>

#include "btor_parser.h"

#include <fstream>
#include <iostream>

/// Convert a BTOR2 sort ID to a CBMC type
static typet sort_to_type(std::size_t sort_id, const btor2_modelt &model)
{
  auto it = model.sorts.find(sort_id);
  if(it == model.sorts.end())
    throw ebmc_errort{} << "BTOR2: unknown sort " << sort_id;

  auto &sort = it->second;
  if(sort.kind == btor2_sortt::kindt::BITVEC)
  {
    if(sort.width == 1)
      return bool_typet{};
    else
      return unsignedbv_typet{sort.width};
  }
  else
  {
    // array
    auto index_type = sort_to_type(sort.index_sort, model);
    auto element_type = sort_to_type(sort.element_sort, model);
    return array_typet{element_type, infinity_exprt{index_type}};
  }
}

/// Convert a BTOR2 node reference to an exprt.
/// Negative references mean bitwise negation.
static exprt node_to_expr(
  std::ptrdiff_t nid,
  const btor2_modelt &model,
  const std::map<std::size_t, exprt> &expr_map)
{
  bool negated = nid < 0;
  auto abs_nid = static_cast<std::size_t>(negated ? -nid : nid);

  auto it = expr_map.find(abs_nid);
  if(it == expr_map.end())
    throw ebmc_errort{} << "BTOR2: undefined node " << abs_nid;

  exprt result = it->second;

  if(negated)
  {
    if(result.type().id() == ID_bool)
      return not_exprt{result};
    else
      return bitnot_exprt{result};
  }

  return result;
}

/// Cast a bool expression to unsignedbv[1] if needed.
/// Many BTOR2 operators (arithmetic, shifts, signed comparisons) require
/// a bitvector operand, but bitvec 1 is mapped to bool_typet.
static exprt to_bv(const exprt &e)
{
  if(e.type().id() == ID_bool)
    return typecast_exprt{e, unsignedbv_typet{1}};
  return e;
}

/// Get the width of a bitvector or bool expression.
static std::size_t get_width(const exprt &e)
{
  if(e.type().id() == ID_bool)
    return 1;
  return to_bitvector_type(e.type()).get_width();
}

/// Cast to signed, widening to at least 2 bits to satisfy CBMC's
/// lt_or_le precondition (signed bitvectors need >= 2 bits).
static exprt to_signed(const exprt &e)
{
  auto a = to_bv(e);
  auto w = get_width(e);
  if(w < 2)
  {
    a = typecast_exprt{a, unsignedbv_typet{2}};
    w = 2;
  }
  return typecast_exprt{a, signedbv_typet{w}};
}

/// Parse a binary constant string to a CBMC constant expression
static constant_exprt
binary_to_const(const std::string &bits, const typet &type)
{
  mp_integer value = 0;
  for(char c : bits)
  {
    value *= 2;
    if(c == '1')
      value += 1;
  }
  if(type.id() == ID_bool)
    return from_integer(value.is_odd() ? 1 : 0, type);
  return from_integer(value, type);
}

/// Parse a decimal constant string to a CBMC constant expression
static constant_exprt
decimal_to_const(const std::string &dec, const typet &type)
{
  mp_integer value;
  if(dec[0] == '-')
    value = -string2integer(dec.substr(1));
  else
    value = string2integer(dec);
  if(type.id() == ID_bool)
    return from_integer(value.is_odd() ? 1 : 0, type);
  return from_integer(value, type);
}

/// Parse a hex constant string to a CBMC constant expression
static constant_exprt hex_to_const(const std::string &hex, const typet &type)
{
  mp_integer value = 0;
  for(char c : hex)
  {
    value *= 16;
    if(c >= '0' && c <= '9')
      value += c - '0';
    else if(c >= 'a' && c <= 'f')
      value += c - 'a' + 10;
    else if(c >= 'A' && c <= 'F')
      value += c - 'A' + 10;
  }
  if(type.id() == ID_bool)
    return from_integer(value.is_odd() ? 1 : 0, type);
  return from_integer(value, type);
}

/// Build a CBMC expression for a BTOR2 operator node
static exprt build_op_expr(
  const btor2_linet &node,
  const typet &type,
  const btor2_modelt &model,
  const std::map<std::size_t, exprt> &expr_map)
{
  auto arg = [&](std::size_t i) -> exprt
  { return node_to_expr(node.args.at(i), model, expr_map); };

  auto require_bv = [&](const exprt &e)
  {
    if(e.type().id() == ID_array)
      throw ebmc_errort{} << "BTOR2: operator '" << node.tag
                          << "' requires bitvector operands";
  };

  const auto &tag = node.tag;

  // Unary operators
  if(tag == "not")
  {
    if(type.id() == ID_bool)
      return not_exprt{arg(0)};
    else
      return bitnot_exprt{arg(0)};
  }

  // Boolean operators
  if(tag == "iff")
    return equal_exprt{arg(0), arg(1)};

  if(tag == "implies")
    return implies_exprt{arg(0), arg(1)};

  if(tag == "eq")
    return equal_exprt{arg(0), arg(1)};

  if(tag == "neq")
    return notequal_exprt{arg(0), arg(1)};

  // Bitwise operators
  if(tag == "and")
  {
    if(type.id() == ID_bool)
      return and_exprt{arg(0), arg(1)};
    else
      return bitand_exprt{arg(0), arg(1)};
  }

  if(tag == "nand")
  {
    if(type.id() == ID_bool)
      return not_exprt{and_exprt{arg(0), arg(1)}};
    else
      return bitnand_exprt{arg(0), arg(1)};
  }

  if(tag == "nor")
  {
    if(type.id() == ID_bool)
      return not_exprt{or_exprt{arg(0), arg(1)}};
    else
      return bitnor_exprt{arg(0), arg(1)};
  }

  if(tag == "or")
  {
    if(type.id() == ID_bool)
      return or_exprt{arg(0), arg(1)};
    else
      return bitor_exprt{arg(0), arg(1)};
  }

  if(tag == "xnor")
  {
    if(type.id() == ID_bool)
      return equal_exprt{arg(0), arg(1)};
    else
      return bitxnor_exprt{arg(0), arg(1)};
  }

  if(tag == "xor")
  {
    if(type.id() == ID_bool)
      return notequal_exprt{arg(0), arg(1)};
    else
      return bitxor_exprt{arg(0), arg(1)};
  }

  // Array operations
  if(tag == "read")
    return index_exprt{arg(0), arg(1)};

  if(tag == "write")
    return with_exprt{arg(0), arg(1), arg(2)};

  // Ternary
  if(tag == "ite")
    return if_exprt{arg(0), arg(1), arg(2)};

  // from here onwards, all operators require all arguments to have vector type
  for(std::size_t i = 0; i < node.args.size(); i++)
    require_bv(arg(i));

  if(tag == "inc")
    return plus_exprt{to_bv(arg(0)), from_integer(1, to_bv(arg(0)).type())};

  if(tag == "dec")
    return minus_exprt{to_bv(arg(0)), from_integer(1, to_bv(arg(0)).type())};

  if(tag == "neg")
    return unary_minus_exprt{to_bv(arg(0)), to_bv(arg(0)).type()};

  if(tag == "redand")
    return reduction_and_exprt{to_bv(arg(0))};

  if(tag == "redor")
    return reduction_or_exprt{to_bv(arg(0))};

  if(tag == "redxor")
    return reduction_xor_exprt{to_bv(arg(0))};

  // Signed/unsigned comparisons
  if(tag == "sgt" || tag == "sgte" || tag == "slt" || tag == "slte")
  {
    auto sa = to_signed(arg(0));
    auto sb = to_signed(arg(1));
    irep_idt rel_id = tag == "sgt"    ? ID_gt
                      : tag == "sgte" ? ID_ge
                      : tag == "slt"  ? ID_lt
                                      : ID_le;
    return binary_relation_exprt{sa, rel_id, sb};
  }

  if(tag == "ugt")
    return binary_relation_exprt{to_bv(arg(0)), ID_gt, to_bv(arg(1))};

  if(tag == "ugte")
    return binary_relation_exprt{to_bv(arg(0)), ID_ge, to_bv(arg(1))};

  if(tag == "ult")
    return binary_relation_exprt{to_bv(arg(0)), ID_lt, to_bv(arg(1))};

  if(tag == "ulte")
    return binary_relation_exprt{to_bv(arg(0)), ID_le, to_bv(arg(1))};

  // Shift and rotate
  if(tag == "sll")
    return shl_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "srl")
    return lshr_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "sra")
    return typecast_exprt{ashr_exprt{to_signed(arg(0)), to_bv(arg(1))}, type};

  if(tag == "rol")
    return shift_exprt{to_bv(arg(0)), ID_rol, to_bv(arg(1))};

  if(tag == "ror")
    return shift_exprt{to_bv(arg(0)), ID_ror, to_bv(arg(1))};

  // Arithmetic
  if(tag == "add")
    return plus_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "sub")
    return minus_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "mul")
    return mult_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "udiv")
    return div_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "sdiv")
  {
    return typecast_exprt{
      div_exprt{to_signed(arg(0)), to_signed(arg(1))}, type};
  }

  if(tag == "urem")
    return mod_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "srem")
  {
    return typecast_exprt{
      mod_exprt{to_signed(arg(0)), to_signed(arg(1))}, type};
  }

  if(tag == "smod")
  {
    // smod: result has sign of divisor
    // smod(a,b) = srem(a,b)==0 ? 0 : (sign(srem)!=sign(b) ? srem+b : srem)
    auto a = to_signed(arg(0));
    auto b = to_signed(arg(1));
    auto signed_type = a.type();
    auto rem = mod_exprt{a, b};
    auto zero = from_integer(0, signed_type);

    // Check if signs differ: (rem < 0) != (b < 0)
    auto rem_neg = binary_relation_exprt{rem, ID_lt, zero};
    auto b_neg = binary_relation_exprt{b, ID_lt, zero};
    auto signs_differ = notequal_exprt{rem_neg, b_neg};
    auto rem_nonzero = notequal_exprt{rem, zero};
    auto adjust = and_exprt{rem_nonzero, signs_differ};
    auto result = if_exprt{adjust, plus_exprt{rem, b}, rem};
    return typecast_exprt{result, type};
  }

  // Concatenation
  if(tag == "concat")
    return concatenation_exprt{to_bv(arg(0)), to_bv(arg(1)), type};

  // Indexed operators
  if(tag == "sext")
  {
    auto a = to_bv(arg(0));
    auto w = get_width(arg(0));
    auto new_width = w + node.uargs.at(0);
    return typecast_exprt{
      typecast_exprt{a, signedbv_typet{w}}, unsignedbv_typet{new_width}};
  }

  if(tag == "uext")
  {
    auto new_width = get_width(arg(0)) + node.uargs.at(0);
    return typecast_exprt{to_bv(arg(0)), unsignedbv_typet{new_width}};
  }

  if(tag == "slice")
  {
    auto upper = node.uargs.at(0);
    auto lower = node.uargs.at(1);
    auto src_width = get_width(arg(0));
    if(upper >= src_width)
      throw ebmc_errort{} << "BTOR2: slice upper index " << upper
                          << " exceeds source width " << src_width;
    if(lower > upper)
      throw ebmc_errort{} << "BTOR2: slice lower index " << lower
                          << " exceeds upper index " << upper;
    if(type.id() == ID_bool)
      return extractbit_exprt{to_bv(arg(0)), lower};
    else
      return extractbits_exprt{to_bv(arg(0)), lower, type};
  }

  // Overflow operators
  if(tag == "uaddo")
    return plus_overflow_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "saddo")
    return plus_overflow_exprt{to_signed(arg(0)), to_signed(arg(1))};

  if(tag == "usubo")
    return minus_overflow_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "ssubo")
    return minus_overflow_exprt{to_signed(arg(0)), to_signed(arg(1))};

  if(tag == "umulo")
    return mult_overflow_exprt{to_bv(arg(0)), to_bv(arg(1))};

  if(tag == "smulo")
    return mult_overflow_exprt{to_signed(arg(0)), to_signed(arg(1))};

  throw ebmc_errort{} << "BTOR2: unsupported operator '" << tag << "'";
}

/// Build the transition system from a parsed BTOR2 model
static transition_systemt build_transition_system(const btor2_modelt &model)
{
  const irep_idt mode = "BTOR2";
  const irep_idt module_id = "btor2::main";

  transition_systemt result;

  // Map from BTOR2 node ID to CBMC expression
  std::map<std::size_t, exprt> expr_map;

  // First pass: create symbols for inputs and states
  for(auto &[id, node] : model.nodes)
  {
    if(node.tag == "input")
    {
      auto type = sort_to_type(node.sort_id, model);
      std::string name =
        node.symbol.empty() ? "input" + std::to_string(id) : node.symbol;
      irep_idt sym_id = id2string(module_id) + "::" + name;

      symbolt symbol{sym_id, type, mode};
      symbol.base_name = name;
      symbol.pretty_name = name;
      symbol.module = module_id;
      symbol.is_input = true;
      symbol.is_state_var = false;

      result.symbol_table.add(symbol);
      expr_map[id] = symbol_exprt{sym_id, type};
    }
    else if(node.tag == "state")
    {
      auto type = sort_to_type(node.sort_id, model);
      std::string name =
        node.symbol.empty() ? "state" + std::to_string(id) : node.symbol;
      irep_idt sym_id = id2string(module_id) + "::" + name;

      symbolt symbol{sym_id, type, mode};
      symbol.base_name = name;
      symbol.pretty_name = name;
      symbol.module = module_id;
      symbol.is_input = false;
      symbol.is_state_var = true;

      result.symbol_table.add(symbol);
      expr_map[id] = symbol_exprt{sym_id, type};
    }
  }

  // Second pass: build expressions for all nodes in order
  for(auto &[id, node] : model.nodes)
  {
    if(expr_map.count(id))
      continue; // already handled (input/state)

    if(
      node.tag == "bad" || node.tag == "constraint" || node.tag == "fair" ||
      node.tag == "output" || node.tag == "justice" || node.tag == "init" ||
      node.tag == "next")
    {
      continue; // handled in later passes
    }

    auto type = sort_to_type(node.sort_id, model);

    // Constants
    if(node.tag == "zero")
    {
      expr_map[id] = from_integer(0, type);
      continue;
    }
    if(node.tag == "one")
    {
      expr_map[id] = from_integer(1, type);
      continue;
    }
    if(node.tag == "ones")
    {
      if(type.id() == ID_bool)
        expr_map[id] = true_exprt{};
      else
      {
        auto width = to_bitvector_type(type).get_width();
        expr_map[id] = from_integer(power(2, width) - 1, type);
      }
      continue;
    }
    if(node.tag == "const")
    {
      expr_map[id] = binary_to_const(node.symbol, type);
      continue;
    }
    if(node.tag == "constd")
    {
      expr_map[id] = decimal_to_const(node.symbol, type);
      continue;
    }
    if(node.tag == "consth")
    {
      expr_map[id] = hex_to_const(node.symbol, type);
      continue;
    }

    // Operators
    auto op_result = build_op_expr(node, type, model, expr_map);
    // Cast unsignedbv[1] back to bool when the node's sort is bitvec 1
    if(type.id() == ID_bool && op_result.type().id() != ID_bool)
      op_result = typecast_exprt{op_result, bool_typet{}};
    expr_map[id] = std::move(op_result);
  }

  // Third pass: build init and trans constraints
  exprt::operandst invar_exprs;
  exprt::operandst init_exprs;
  exprt::operandst trans_exprs;

  for(auto &[id, node] : model.nodes)
  {
    if(node.tag == "init")
    {
      // init <sid> <state_nid> <value_nid>
      auto state_expr = node_to_expr(node.args[0], model, expr_map);
      auto value_expr = node_to_expr(node.args[1], model, expr_map);
      init_exprs.push_back(equal_exprt{state_expr, value_expr});
    }
    else if(node.tag == "next")
    {
      // next <sid> <state_nid> <next_value_nid>
      auto state_expr = node_to_expr(node.args[0], model, expr_map);
      auto next_value = node_to_expr(node.args[1], model, expr_map);
      if(state_expr.id() != ID_symbol)
        throw ebmc_errort{} << "BTOR2: first argument of 'next' must be a "
                               "state variable (node "
                            << id << ")";
      next_symbol_exprt next_state{to_symbol_expr(state_expr)};
      trans_exprs.push_back(equal_exprt{next_state, next_value});
    }
  }

  // Constraints become invariants
  for(auto constraint_id : model.constraints)
  {
    auto &node = model.nodes.at(constraint_id);
    auto constraint_expr = node_to_expr(node.args[0], model, expr_map);
    // If not bool, convert to bool (non-zero means true)
    if(constraint_expr.type().id() != ID_bool)
    {
      constraint_expr = notequal_exprt{
        constraint_expr, from_integer(0, constraint_expr.type())};
    }
    invar_exprs.push_back(constraint_expr);
  }

  // Bad state properties: G(!bad)
  for(auto bad_id : model.bad_properties)
  {
    auto &node = model.nodes.at(bad_id);
    auto bad_expr = node_to_expr(node.args[0], model, expr_map);

    if(bad_expr.type().id() != ID_bool)
      bad_expr = notequal_exprt{bad_expr, from_integer(0, bad_expr.type())};

    std::string name =
      node.symbol.empty() ? "bad" + std::to_string(bad_id) : node.symbol;
    irep_idt prop_id = id2string(module_id) + "::spec::" + name;

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{not_exprt{bad_expr}};

    result.symbol_table.add(prop_symbol);
  }

  // Fair properties: G(F(fair))
  for(auto fair_id : model.fair_properties)
  {
    auto &node = model.nodes.at(fair_id);
    auto fair_expr = node_to_expr(node.args[0], model, expr_map);

    if(fair_expr.type().id() != ID_bool)
      fair_expr = notequal_exprt{fair_expr, from_integer(0, fair_expr.type())};

    std::string name =
      node.symbol.empty() ? "fair" + std::to_string(fair_id) : node.symbol;
    irep_idt prop_id = id2string(module_id) + "::spec::" + name;

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{F_exprt{fair_expr}};

    result.symbol_table.add(prop_symbol);
  }

  // Justice properties: G(F(conjunction))
  for(auto justice_id : model.justice_properties)
  {
    auto &node = model.nodes.at(justice_id);

    exprt::operandst conjuncts;
    for(auto arg : node.args)
    {
      auto e = node_to_expr(arg, model, expr_map);
      if(e.type().id() != ID_bool)
        e = notequal_exprt{e, from_integer(0, e.type())};
      conjuncts.push_back(e);
    }

    std::string name = "justice" + std::to_string(justice_id);
    irep_idt prop_id = id2string(module_id) + "::spec::" + name;

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{F_exprt{conjunction(conjuncts)}};

    result.symbol_table.add(prop_symbol);
  }

  // Module symbol
  typet module_type(ID_module);

  symbolt module_symbol{module_id, module_type, mode};
  module_symbol.base_name = "main";
  module_symbol.pretty_name = "main";
  module_symbol.module = module_id;
  module_symbol.value = transt{
    ID_trans,
    conjunction(invar_exprs),
    conjunction(init_exprs),
    conjunction(trans_exprs),
    module_type};

  result.symbol_table.add(module_symbol);

  result.main_symbol = &result.symbol_table.lookup_ref(module_id);
  result.trans_expr = to_trans_expr(result.main_symbol->value);

  return result;
}

std::optional<transition_systemt> btor_ebmc_languaget::transition_system()
{
  if(cmdline.args.empty())
    throw ebmc_errort{} << "no file name given";

  if(cmdline.args.size() >= 2)
    throw ebmc_errort{}.with_exit_code(1) << "BTOR2 only uses a single file";

  const auto &file_name = cmdline.args.front();

  std::ifstream in(file_name);
  if(!in)
  {
    throw ebmc_errort{}.with_exit_code(1) << "failed to open " << file_name;
  }

  auto model = btor2_parse(in);

  if(cmdline.isset("show-parse"))
  {
    btor2_show_parse(model, std::cout);
    return {};
  }

  auto result = build_transition_system(model);

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << result.symbol_table;
    return {};
  }

  return result;
}
