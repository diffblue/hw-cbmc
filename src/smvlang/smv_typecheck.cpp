/*******************************************************************\

Module: SMV Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_typecheck.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/typecheck.h>

#include "expr2smv.h"
#include "smv_expr.h"
#include "smv_range.h"
#include "smv_types.h"

#include <algorithm>
#include <cassert>
#include <set>

class smv_typecheckt:public typecheckt
{
public:
  smv_typecheckt(
    smv_parse_treet &_smv_parse_tree,
    symbol_table_baset &_symbol_table,
    const std::string &_module,
    bool _do_spec,
    message_handlert &_message_handler)
    : typecheckt(_message_handler),
      smv_parse_tree(_smv_parse_tree),
      symbol_table(_symbol_table),
      module(_module),
      do_spec(_do_spec)
  {
    nondet_count=0;
  }

  ~smv_typecheckt() override
  {
  }

  typedef enum
  {
    INIT,
    INVAR,
    TRANS,
    OTHER,
    LTL,
    CTL
  } modet;

  void convert(smv_parse_treet::modulet &);

  void create_var_symbols(const smv_parse_treet::modulet::element_listt &);

  void collect_define(const exprt &lhs, const exprt &rhs);
  void convert_defines(exprt::operandst &invar);
  void convert_define(const irep_idt &identifier);

  void convert(exprt &);

  void typecheck(exprt &, modet);
  void typecheck_op(exprt &, const typet &, modet);

  void typecheck() override;

  // These output SMV syntax
  std::string to_string(const typet &);
  std::string to_string(const exprt &);

protected:
  smv_parse_treet &smv_parse_tree;
  symbol_table_baset &symbol_table;
  const std::string &module;
  bool do_spec;

  void check_type(typet &);
  smv_ranget convert_type(const typet &);

  void variable_checks(const smv_parse_treet::modulet &);
  bool uses_next(const exprt &expr) const;
  void no_next_allowed(const exprt &expr) const;

  void convert(smv_parse_treet::modulet::elementt &);
  void typecheck(smv_parse_treet::modulet::elementt &);
  void typecheck_expr_rec(exprt &, modet, bool next);
  void convert_expr_to(exprt &, const typet &dest);
  exprt convert_word_constant(const constant_exprt &);

  smv_parse_treet::modulet *modulep;

  unsigned nondet_count;

  void flatten_hierarchy(smv_parse_treet::modulet &);

  void instantiate(
    smv_parse_treet::modulet &,
    const irep_idt &identifier,
    const irep_idt &instance,
    const exprt::operandst &arguments,
    const source_locationt &);

  typet
  type_union(const typet &type1, const typet &type2, const source_locationt &);

  typedef std::map<irep_idt, exprt> rename_mapt;

  void convert_ports(smv_parse_treet::modulet &, typet &dest);

  // for defines
  class definet
  {
  public:
    exprt value;
    bool typechecked = false, in_progress = false, uses_next = false;

    explicit definet(const exprt &_v) : value(_v)
    {
    }

    definet()
    {
    }
  };
  
  typedef std::unordered_map<irep_idt, definet, irep_id_hash> define_mapt;
  define_mapt define_map;

  static irep_idt strip_smv_prefix(irep_idt id)
  {
    if(id.starts_with("smv::"))
      return std::string(id2string(id), 5, std::string::npos);
    else
      return id;
  }

  void lower_node(exprt &) const;

  void lower(typet &) const;

  void lower(exprt &expr) const
  {
    expr.visit_post([this](exprt &expr) { lower_node(expr); });
  }
};

/*******************************************************************\

Function: merge_complex_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt merge_complex_identifier(const exprt &expr)
{
  if(expr.id() == ID_smv_identifier)
    return to_smv_identifier_expr(expr).identifier();
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    return id2string(merge_complex_identifier(member_expr.compound())) + '.' +
           id2string(member_expr.get_component_name());
  }
  else if(expr.id() == ID_index)
  {
    auto &index_expr = to_index_expr(expr);
    auto &index = index_expr.index();
    PRECONDITION(index.is_constant());
    auto index_string = id2string(to_constant_expr(index).get_value());
    return id2string(merge_complex_identifier(index_expr.array())) + '.' +
           index_string;
  }
  else
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      false, "unexpected complex_identifier", expr.pretty());
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert_ports

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert_ports(
  smv_parse_treet::modulet &smv_module,
  typet &dest)
{
  irept::subt &ports=dest.add(ID_ports).get_sub();

  ports.reserve(smv_module.parameters.size());

  for(const auto &port_name : smv_module.parameters)
  {
    ports.push_back(exprt(ID_symbol));
    ports.back().set(
      ID_identifier,
      id2string(smv_module.name) + "::var::" + id2string(port_name));
  }
}

/*******************************************************************\

Function: smv_typecheckt::flatten_hierarchy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::flatten_hierarchy(smv_parse_treet::modulet &smv_module)
{
  // Not using ranged for since we will append to the list we are
  // iterating over! This avoids recursion.
  for(auto element_it = smv_module.elements.begin();
      element_it != smv_module.elements.end();
      ++element_it)
  {
    auto &element = *element_it;

    if(element.is_var() && element.expr.type().id() == ID_smv_module_instance)
    {
      auto &instance = to_smv_module_instance_type(element.expr.type());

      for(auto &argument : instance.arguments())
        convert(argument);

      auto instance_base_name =
        to_smv_identifier_expr(element.expr).identifier();

      instantiate(
        smv_module,
        instance.identifier(),
        instance_base_name,
        instance.arguments(),
        instance.source_location());
    }
  }
}

/*******************************************************************\

Function: smv_typecheckt::instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::instantiate(
  smv_parse_treet::modulet &smv_module,
  const irep_idt &identifier,
  const irep_idt &instance,
  const exprt::operandst &arguments,
  const source_locationt &location)
{
  // Find the module
  auto module_it = smv_parse_tree.module_map.find(identifier);

  if(module_it == smv_parse_tree.module_map.end())
  {
    throw errort().with_location(location)
      << "submodule `" << identifier << "' not found";
  }

  const auto &instantiated_module = *module_it->second;
  const auto &parameters = instantiated_module.parameters;

  // map the arguments to parameters
  if(parameters.size() != arguments.size())
  {
    throw errort().with_location(location)
      << "submodule `" << identifier << "' has wrong number of arguments";
  }

  rename_mapt parameter_map;

  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    parameter_map.emplace(parameters[i], arguments[i]);
  }

  // We add a prefix to all identifiers in the instantiated
  // module -- this prefix is called "context" in Sec. 2.3.16 in
  // the NuSMV 2.7 manual.
  const std::string context = id2string(instance) + '.';

  // copy the parse tree elements
  for(auto &src_element : instantiated_module.elements)
  {
    auto copy = src_element;

    // replace the parameter identifiers,
    // and add the context prefix to non-parameter, non-enum identifiers
    copy.expr.visit_post(
      [&parameter_map, &context, this](exprt &expr)
      {
        if(expr.id() == ID_smv_identifier)
        {
          auto identifier = to_smv_identifier_expr(expr).identifier();
          auto parameter_it = parameter_map.find(identifier);
          if(parameter_it != parameter_map.end())
          {
            // It's a parameter
            expr = parameter_it->second;
          }
          else if(
            smv_parse_tree.enum_set.find(identifier) !=
            smv_parse_tree.enum_set.end())
          {
            // It's an enum, leave as is
          }
          else
          {
            // add the context prefix
            to_smv_identifier_expr(expr).identifier(
              context + id2string(identifier));
          }
        }
      });

    // add to main parse tree
    smv_module.elements.push_back(copy);
  }
}

/*******************************************************************\

Function: smv_typecheckt::check_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::check_type(typet &type)
{
  if(type.id() == ID_smv_array)
  {
    auto from = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_from))));
    auto to = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_to))));

    if(to < from)
      throw errort().with_location(type.source_location())
        << "array must end with number >= `" << from << '\'';

    type.id(ID_array);
    type.remove(ID_from);
    type.remove(ID_to);
    type.set(ID_size, integer2string(to - from + 1));
    type.set(ID_offset, integer2string(from));

    // recursive call
    check_type(to_type_with_subtype(type).subtype());
  }
  else if(type.id() == ID_smv_enumeration)
  {
    // normalize the ordering of elements
    to_smv_enumeration_type(type).normalize();
  }
  else if(type.id() == ID_smv_range)
  {
    auto from = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_from))));
    auto to = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_to))));

    if(from > to)
      throw errort().with_location(type.source_location()) << "range is empty";

    type.id(ID_range);
    type.set(ID_from, integer2string(from));
    type.set(ID_to, integer2string(to));
  }
  else if(type.id() == ID_smv_signed_word)
  {
    auto width = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_width))));

    if(width < 1)
      throw errort().with_location(type.source_location())
        << "word width must be 1 or larger";

    type.id(ID_signedbv);
    type.set(ID_width, integer2string(width));
  }
  else if(type.id() == ID_smv_word || type.id() == ID_smv_unsigned_word)
  {
    auto width = numeric_cast_v<mp_integer>(
      to_constant_expr(static_cast<const exprt &>(type.find(ID_width))));

    if(width < 1)
      throw errort().with_location(type.source_location())
        << "word width must be 1 or larger";

    type.id(ID_unsignedbv);
    type.set(ID_width, integer2string(width));
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smv_ranget smv_typecheckt::convert_type(const typet &src)
{
  if(src.id()==ID_bool)
  {
    return {0, 1};
  }
  else if(src.id()==ID_range)
  {
    return smv_ranget::from_type(to_range_type(src));
  }
  else if(src.id() == ID_smv_enumeration)
  {
    smv_ranget dest;

    dest.from=0;

    std::size_t number_of_elements =
      to_smv_enumeration_type(src).elements().size();

    if(number_of_elements==0)
      dest.to=0;
    else
      dest.to=(long long)number_of_elements-1;

    return dest;
  }
  else
  {
    throw errort().with_location(src.source_location())
      << "Unexpected type: `" << to_string(src) << "'";
  }
}

/*******************************************************************\

Function: smv_typecheckt::type_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet smv_typecheckt::type_union(
  const typet &type1,
  const typet &type2,
  const source_locationt &source_location)
{
  if(type1==type2) return type1;

  if(type1.is_nil())
    return type2;

  if(type2.is_nil())
    return type1;

  if(
    type1.id() == ID_signedbv || type1.id() == ID_unsignedbv ||
    type2.id() == ID_signedbv || type2.id() == ID_unsignedbv)
  {
    throw errort().with_location(source_location)
      << "no type union for types " << to_string(type1) << " and "
      << to_string(type2);
  }

  // both enums?
  if(type1.id() == ID_smv_enumeration && type2.id() == ID_smv_enumeration)
  {
    auto &e_type1 = to_smv_enumeration_type(type1);
    auto &e_type2 = to_smv_enumeration_type(type2);

    return ::type_union(e_type1, e_type2);
  }

  // one of them enum?
  if(type1.id() == ID_smv_enumeration || type2.id() == ID_smv_enumeration)
  {
    throw errort().with_location(source_location)
      << "no type union for types " << to_string(type1) << " and "
      << to_string(type2);
  }

  smv_ranget range1=convert_type(type1);
  smv_ranget range2=convert_type(type2);

  range1.make_union(range2);
  
  if((type1.id()==ID_bool || type2.id()==ID_bool) &&
     range1.is_bool())
  {
    return bool_typet();
  }
  else
  {
    return range1.to_type();
  }
}

/*******************************************************************\

Function: smv_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck(exprt &expr, modet mode)
{
  typecheck_expr_rec(expr, mode, false);
}

/*******************************************************************\

Function: convert_word_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt smv_typecheckt::convert_word_constant(const constant_exprt &src_expr)
{
  auto &src = id2string(src_expr.get_value());

  DATA_INVARIANT(src[0] == '0', "word constant grammar");

  std::size_t index = 1;
  bool is_signed = false;

  DATA_INVARIANT(index < src.size(), "word constant length");

  switch(src[index])
  {
  case 's':
  case 'S':
    is_signed = true;
    index++;
    break;

  case 'u':
  case 'U':
    // this is the default
    index++;
    break;

  default:;
  }

  DATA_INVARIANT(index < src.size(), "word constant length");

  unsigned base;
  switch(src[index])
  {
  case 'd':
  case 'D':
    base = 10;
    break;

  case 'h':
  case 'H':
    base = 16;
    break;

  case 'b':
  case 'B':
    base = 2;
    break;

  case 'o':
  case 'O':
    base = 8;
    break;

  default:
    DATA_INVARIANT(false, "word constant base");
  }

  index++;

  DATA_INVARIANT(index < src.size(), "word constant length");

  std::optional<mp_integer> bits = {};

  // optional number of bits
  if(isdigit(src[index]))
  {
    std::string bits_str;
    for(; index < src.size() && isdigit(src[index]); index++)
    {
      bits_str += src[index];
    }

    bits = string2integer(bits_str);
  }

  std::string digits;
  digits.reserve(src.size());

  for(; index < src.size(); index++)
  {
    if(src[index] != '_')
      digits.push_back(src[index]);
  }

  if(!bits.has_value())
  {
    if(base == 10)
      throw errort{}.with_location(src_expr.source_location())
        << "decimal word constant without width";
    else if(base == 2)
      bits = digits.size();
    else if(base == 8)
      bits = digits.size() * 3;
    else if(base == 16)
      bits = digits.size() * 4;
  }

  auto digits_int = string2integer(digits, base);

  auto type =
    bitvector_typet{is_signed ? ID_signedbv : ID_unsignedbv, bits.value()};

  return from_integer(digits_int, type).with_source_location(src_expr);
}

/*******************************************************************\

Function: smv_typecheckt::typecheck_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck_expr_rec(exprt &expr, modet mode, bool next)
{
  if(expr.id() == ID_smv_next)
  {
    if(next)
    {
      throw errort().with_location(expr.find_source_location())
        << "next(next(...)) encountered";
    }

    expr = to_unary_expr(expr).op();

    typecheck_expr_rec(expr, mode, true);
  }
  else if(expr.id() == ID_symbol || expr.id() == ID_next_symbol)
  {
    const irep_idt &identifier = expr.get(ID_identifier);

    if(define_map.find(identifier)!=define_map.end())
      convert_define(identifier);

    auto s_it=symbol_table.get_writeable(identifier);

    if(s_it==nullptr)
    {
      throw errort().with_location(expr.find_source_location())
        << "variable `" << identifier << "' not found";
    }

    if(next)
      expr.id(ID_next_symbol);

    symbolt &symbol=*s_it;
    
    assert(symbol.type.is_not_nil());
    expr.type()=symbol.type;

    if(mode == INIT || next)
    {
      if(symbol.module==module)
      {
        symbol.is_input=false;
        symbol.is_state_var=true;
      }
    }
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_xor ||
    expr.id() == ID_xnor || expr.id() == ID_not || expr.id() == ID_implies)
  {
    PRECONDITION(!expr.operands().empty());

    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode, next);

    auto &op0_type = to_multi_ary_expr(expr).op0().type();

    // boolean or bit-wise?
    if(op0_type.id() == ID_signedbv || op0_type.id() == ID_unsignedbv)
    {
      auto new_id = irep_idt();

      if(expr.id() == ID_and)
        new_id = ID_bitand;
      else if(expr.id() == ID_or)
        new_id = ID_bitor;
      else if(expr.id() == ID_xor)
        new_id = ID_bitxor;
      else if(expr.id() == ID_xnor)
        new_id = ID_bitxnor;
      else if(expr.id() == ID_not)
        new_id = ID_bitnot;
      else if(expr.id() == ID_implies)
        new_id = ID_smv_bitimplies;
      else
        new_id = expr.id();

      expr.id(new_id);

      expr.type() = op0_type;
    }
    else
    {
      expr.type() = bool_typet{};
    }

    for(auto &op : expr.operands())
      convert_expr_to(op, expr.type());
  }
  else if(expr.id() == ID_smv_iff)
  {
    auto &binary_expr = to_binary_expr(expr);
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);

    auto &op0_type = binary_expr.op0().type();

    if(op0_type.id() == ID_signedbv || op0_type.id() == ID_unsignedbv)
    {
      expr.set(ID_C_smv_iff, true);
      expr.id(ID_bitxnor);
      convert_expr_to(binary_expr.rhs(), op0_type);
      expr.type() = op0_type;
    }
    else
    {
      expr.type() = bool_typet{};
      convert_expr_to(binary_expr.lhs(), expr.type());
      convert_expr_to(binary_expr.rhs(), expr.type());
      expr.set(ID_C_smv_iff, true);
      expr.id(ID_equal);
    }
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode, next);

    typet op_type;
    op_type.make_nil();

    for(const auto &op : expr.operands())
    {
      typet tmp = type_union(op.type(), op_type, expr.source_location());
      op_type=tmp;
    }

    for(auto &op : expr.operands())
      convert_expr_to(op, op_type);

    expr.type()=op_type;
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_lt || expr.id()==ID_le ||
          expr.id()==ID_gt || expr.id()==ID_ge)
  {
    expr.type() = bool_typet{};

    exprt &op0 = to_binary_expr(expr).op0();
    exprt &op1 = to_binary_expr(expr).op1();

    typecheck_expr_rec(op0, mode, next);
    typecheck_expr_rec(op1, mode, next);

    typet op_type = type_union(op0.type(), op1.type(), expr.source_location());

    convert_expr_to(op0, op_type);
    convert_expr_to(op1, op_type);

    INVARIANT(op0.type() == op1.type(), "type of operands of relational operators");

    if(expr.id()==ID_lt || expr.id()==ID_le ||
       expr.id()==ID_gt || expr.id()==ID_ge)
    {
      if(
        op0.type().id() != ID_range && op0.type().id() != ID_signedbv &&
        op0.type().id() != ID_unsignedbv)
      {
        throw errort().with_location(expr.find_source_location())
          << "Expected number type for " << to_string(expr);
      }
    }
  }
  else if(expr.id() == ID_if) // ?:
  {
    auto &if_expr = to_if_expr(expr);
    auto &true_case = if_expr.true_case();
    auto &false_case = if_expr.false_case();
    typecheck_expr_rec(if_expr.cond(), mode, next);
    convert_expr_to(if_expr.cond(), bool_typet{});
    typecheck_expr_rec(true_case, mode, next);
    typecheck_expr_rec(false_case, mode, next);
    expr.type() =
      type_union(true_case.type(), false_case.type(), expr.source_location());
    convert_expr_to(true_case, expr.type());
    convert_expr_to(false_case, expr.type());
  }
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult || expr.id()==ID_div ||
          expr.id()==ID_mod)
  {
    auto &op0 = to_binary_expr(expr).op0();
    auto &op1 = to_binary_expr(expr).op1();

    typecheck_expr_rec(op0, mode, next);
    typecheck_expr_rec(op1, mode, next);

    if(op0.type().id() == ID_range || op0.type().id() == ID_bool)
    {
      // find proper type for precise arithmetic
      smv_ranget new_range;

      smv_ranget smv_range0 = convert_type(op0.type());
      smv_ranget smv_range1 = convert_type(op1.type());

      if(expr.id() == ID_plus)
        new_range = smv_range0 + smv_range1;
      else if(expr.id() == ID_minus)
        new_range = smv_range0 - smv_range1;
      else if(expr.id() == ID_mult)
        new_range = smv_range0 * smv_range1;
      else if(expr.id() == ID_div)
      {
        throw errort().with_location(expr.source_location())
          << "no support for / on integer operands";
      }
      else if(expr.id() == ID_mod)
      {
        throw errort().with_location(expr.source_location())
          << "no support for % on integer operands";
      }
      else
        assert(false);

      auto location = expr.source_location();
      auto final_type = type_union(
        new_range.to_type(),
        type_union(op0.type(), op1.type(), location),
        location);
      expr.type() = final_type;

      convert_expr_to(op0, final_type);
      convert_expr_to(op1, final_type);
    }
    else if(op0.type().id() == ID_signedbv || op0.type().id() == ID_unsignedbv)
    {
      expr.type() = op0.type();
      convert_expr_to(op1, op0.type());
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "arithmetic operator requires integer or word type operands";
    }
  }
  else if(expr.id()==ID_constant)
  {
    const auto value = to_constant_expr(expr).get_value();
    auto &type = expr.type();

    if(type.id() == ID_integer)
    {
      mp_integer int_value = string2integer(id2string(value));
      expr.type() = range_typet{int_value, int_value};
    }
    else if(type.id() == ID_smv_enumeration)
    {
      auto t = smv_enumeration_typet{{value}};
      expr.type() = std::move(t);
    }
    else if(type.id() == ID_bool)
    {
      // good as is
    }
    else if(type.id() == ID_smv_word_constant)
    {
      // turn into signedbv/unsignedbv
      expr = convert_word_constant(to_constant_expr(expr));
    }
    else
    {
      PRECONDITION(false);
    }
  }
  else if(expr.id()==ID_cond)
  {
    // case ... esac
    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode, next);

    bool condition = true;

    expr.type().make_nil();

    for(auto &op : expr.operands())
    {
      if(!condition)
        expr.type() =
          type_union(expr.type(), op.type(), expr.source_location());

      condition = !condition;
    }

    // go again, re-type the operands
    condition = true;

    for(auto &op : expr.operands())
    {
      if(condition)
        convert_expr_to(op, bool_typet{});
      else
        convert_expr_to(op, expr.type());

      condition = !condition;
    }
  }
  else if(
    expr.id() == ID_AG || expr.id() == ID_AX || expr.id() == ID_AF ||
    expr.id() == ID_EG || expr.id() == ID_EX || expr.id() == ID_EF)
  {
    if(mode != CTL)
      throw errort().with_location(expr.source_location())
        << "CTL operator not permitted here";
    expr.type() = bool_typet();
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    convert_expr_to(op, expr.type());
  }
  else if(
    expr.id() == ID_smv_EBF || expr.id() == ID_smv_ABF ||
    expr.id() == ID_smv_EBG || expr.id() == ID_smv_ABG)
  {
    if(mode != CTL)
      throw errort().with_location(expr.source_location())
        << "CTL operator not permitted here";
    expr.type() = bool_typet();
    auto &op2 = to_ternary_expr(expr).op2();
    typecheck_expr_rec(op2, mode, next);
    convert_expr_to(op2, expr.type());
  }
  else if(expr.id() == ID_smv_ABU || expr.id() == ID_smv_EBU)
  {
    if(mode != CTL)
      throw errort().with_location(expr.source_location())
        << "CTL operator not permitted here";
    expr.type() = bool_typet();
    for(std::size_t i = 0; i < expr.operands().size(); i++)
    {
      typecheck_expr_rec(expr.operands()[i], mode, next);
      if(i == 0 || i == 3)
        convert_expr_to(expr.operands()[i], expr.type());
    }
  }
  else if(
    expr.id() == ID_X || expr.id() == ID_F || expr.id() == ID_G ||
    expr.id() == ID_smv_H || expr.id() == ID_smv_O || expr.id() == ID_smv_Y ||
    expr.id() == ID_smv_Z)
  {
    if(mode != LTL)
      throw errort().with_location(expr.source_location())
        << "LTL operator not permitted here";
    expr.type() = bool_typet{};
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    convert_expr_to(op, expr.type());
  }
  else if(
    expr.id() == ID_EU || expr.id() == ID_ER || expr.id() == ID_AU ||
    expr.id() == ID_AR)
  {
    if(mode != CTL)
      throw errort().with_location(expr.source_location())
        << "CTL operator not permitted here";
    auto &binary_expr = to_binary_expr(expr);
    expr.type() = bool_typet{};
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    convert_expr_to(binary_expr.lhs(), expr.type());
    convert_expr_to(binary_expr.rhs(), expr.type());
  }
  else if(
    expr.id() == ID_U || expr.id() == ID_R || expr.id() == ID_smv_S ||
    expr.id() == ID_smv_T)
  {
    if(mode != LTL)
      throw errort().with_location(expr.source_location())
        << "LTL operator not permitted here";
    auto &binary_expr = to_binary_expr(expr);
    expr.type() = bool_typet{};
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    convert_expr_to(binary_expr.lhs(), expr.type());
    convert_expr_to(binary_expr.rhs(), expr.type());
  }
  else if(expr.id()==ID_typecast)
  {
    // only get added by type checker
    PRECONDITION(false);
  }
  else if(expr.id() == ID_smv_setin)
  {
    auto &lhs = to_binary_expr(expr).lhs();
    auto &rhs = to_binary_expr(expr).rhs();

    typecheck_expr_rec(lhs, mode, next);
    typecheck_expr_rec(rhs, mode, next);

    // The RHS can be a set or a singleton
    if(rhs.type().id() == ID_smv_set)
    {
      PRECONDITION(rhs.id() == ID_smv_set);
      // do type union
      typet op_type = lhs.type();
      for(auto &op : rhs.operands())
        op_type = type_union(op_type, op.type(), expr.source_location());
      // now convert
      convert_expr_to(lhs, op_type);
      for(auto &op : rhs.operands())
        convert_expr_to(op, op_type);
    }
    else
    {
      typet op_type =
        type_union(lhs.type(), rhs.type(), expr.source_location());

      convert_expr_to(lhs, op_type);
      convert_expr_to(rhs, op_type);
    }

    expr.type() = bool_typet();
  }
  else if(expr.id() == ID_smv_setnotin)
  {
    expr.type()=bool_typet();
  }
  else if(expr.id() == ID_unary_minus)
  {
    auto &uminus_expr = to_unary_minus_expr(expr);
    typecheck_expr_rec(uminus_expr.op(), mode, next);
    auto &op_type = uminus_expr.op().type();

    if(op_type.id() == ID_range)
    {
      uminus_expr.type() =
        (-smv_ranget::from_type(to_range_type(op_type))).to_type();
    }
    else if(op_type.id() == ID_signedbv || op_type.id() == ID_unsignedbv)
    {
      uminus_expr.type() = op_type;
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "Operand to unary minus must be integer or word type, but got "
        << to_string(op_type);
    }

    // constant folding
    if(uminus_expr.op().is_constant())
      expr = from_integer(
        -numeric_cast_v<mp_integer>(to_constant_expr(uminus_expr.op())),
        uminus_expr.type());
  }
  else if(expr.id() == ID_smv_swconst)
  {
    auto &binary_expr = to_binary_expr(expr);
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    PRECONDITION(binary_expr.lhs().is_constant());
    PRECONDITION(binary_expr.rhs().is_constant());
    auto bits = numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.rhs()));
    auto type = signedbv_typet{bits};
    auto value =
      numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.lhs()));
    expr =
      from_integer(value, type).with_source_location(expr.source_location());
  }
  else if(expr.id() == ID_smv_uwconst)
  {
    auto &binary_expr = to_binary_expr(expr);
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    PRECONDITION(binary_expr.lhs().is_constant());
    PRECONDITION(binary_expr.rhs().is_constant());
    auto bits = numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.rhs()));
    auto type = unsignedbv_typet{bits};
    auto value =
      numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.lhs()));
    expr =
      from_integer(value, type).with_source_location(expr.source_location());
  }
  else if(expr.id() == ID_smv_abs)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() == ID_range)
    {
      // ok
      auto &range_type = to_range_type(op.type());
      auto abs = [](mp_integer i)
      {
        if(i < 0)
          i.negate();
        return i;
      };
      expr.type() =
        range_typet{abs(range_type.get_from()), abs(range_type.get_to())};
    }
    else
    {
      throw errort().with_location(expr.source_location())
        << "abs expects integer";
    }
  }
  else if(expr.id() == ID_smv_bit_selection) // word[high:low]
  {
    auto &op = to_ternary_expr(expr).op0();

    typecheck_expr_rec(op, mode, next);

    if(op.type().id() != ID_unsignedbv && op.type().id() != ID_signedbv)
    {
      throw errort().with_location(op.source_location())
        << "bit selection expects word";
    }

    auto &high = to_ternary_expr(expr).op1();

    typecheck_expr_rec(high, OTHER, next);

    // high must be an integer constant
    if(high.type().id() != ID_range && high.type().id() != ID_natural)
    {
      throw errort().with_location(expr.find_source_location())
        << "bit-select high must be integer, but got "
        << to_string(high.type());
    }

    if(high.id() != ID_constant)
      throw errort().with_location(expr.find_source_location())
        << "bit-select high must be constant";

    auto high_int = numeric_cast_v<mp_integer>(to_constant_expr(high));

    auto &low = to_ternary_expr(expr).op2();

    typecheck_expr_rec(low, OTHER, next);

    // low must be an integer constant
    if(low.type().id() != ID_range && low.type().id() != ID_natural)
    {
      throw errort().with_location(expr.find_source_location())
        << "bit-select low must be integer, but got " << to_string(low.type());
    }

    if(low.id() != ID_constant)
      throw errort().with_location(expr.find_source_location())
        << "bit-select low must be constant";

    auto low_int = numeric_cast_v<mp_integer>(to_constant_expr(low));

    if(low_int > high_int)
      throw errort().with_location(expr.find_source_location())
        << "bit-select high must not be smaller than low";

    auto width = numeric_cast_v<std::size_t>(high_int - low_int + 1);

    // always unsigned, even if op is signed
    expr.type() = unsignedbv_typet{width};
  }
  else if(expr.id() == ID_smv_bool)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(
      op.type().id() == ID_bool || op.type().id() == ID_unsignedbv ||
      op.type().id() == ID_signedbv || op.type().id() == ID_range)
    {
      // ok
    }
    else
      throw errort().with_location(expr.source_location())
        << "bool expects boolean, integer or word";

    expr.type() = bool_typet{};
  }
  else if(expr.id() == ID_smv_count)
  {
    auto &multi_ary_expr = to_multi_ary_expr(expr);
    for(auto &op : multi_ary_expr.operands())
    {
      typecheck_expr_rec(op, mode, next);
      if(op.type().id() != ID_bool)
        throw errort().with_location(op.source_location())
          << "count expects boolean arguments";
    }
    expr.type() = range_typet{0, multi_ary_expr.operands().size()};
  }
  else if(expr.id() == ID_smv_max || expr.id() == ID_smv_min)
  {
    auto &binary_expr = to_binary_expr(expr);

    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);

    binary_expr.type() = type_union(
      binary_expr.lhs().type(),
      binary_expr.rhs().type(),
      expr.source_location());

    if(binary_expr.type().id() == ID_range)
    {
      // ok
    }
    else
      throw errort().with_location(expr.source_location())
        << "min/max expect integers";

    convert_expr_to(binary_expr.lhs(), binary_expr.type());
    convert_expr_to(binary_expr.rhs(), binary_expr.type());
  }
  else if(expr.id() == ID_smv_toint)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() == ID_bool)
    {
      expr.type() = range_typet{0, 1};
    }
    else if(op.type().id() == ID_unsignedbv || op.type().id() == ID_signedbv)
    {
      auto &op_type = to_integer_bitvector_type(op.type());
      expr.type() = range_typet{op_type.smallest(), op_type.largest()};
    }
    else if(op.type().id() == ID_range)
    {
      // leave as is
      expr.type() = op.type();
    }
    else
      throw errort().with_location(expr.source_location())
        << "toint expects boolean, integer or word";
  }
  else if(expr.id() == ID_smv_word1)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() != ID_bool)
      throw errort().with_location(op.source_location())
        << "word1 expects boolean argument";
    expr.type() = unsignedbv_typet{1};
  }
  else if(
    expr.id() == ID_shr || expr.id() == ID_shl || expr.id() == ID_lshr ||
    expr.id() == ID_ashr)
  {
    auto &binary_expr = to_binary_expr(expr);

    // The LHS must be a word type.
    typecheck_expr_rec(binary_expr.lhs(), mode, next);

    binary_expr.type() = binary_expr.lhs().type();

    if(binary_expr.type().id() == ID_signedbv)
    {
      if(expr.id() == ID_shr)
        expr.id(ID_ashr);
    }
    else if(binary_expr.type().id() == ID_unsignedbv)
    {
      if(expr.id() == ID_shr)
        expr.id(ID_lshr);
    }
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "Shift operand must be word type";
    }

    // The RHS must be an integer constant
    typecheck_expr_rec(binary_expr.rhs(), mode, next);

    if(
      binary_expr.rhs().type().id() != ID_range &&
      binary_expr.rhs().type().id() != ID_natural)
      throw errort().with_location(expr.find_source_location())
        << "Shift distance must be integer, but got "
        << to_string(binary_expr.rhs().type());

    if(binary_expr.rhs().id() != ID_constant)
      throw errort().with_location(expr.find_source_location())
        << "Shift distance must be constant";

    // distance must be 0...w, where w is the number of bits of the LHS
    auto distance =
      numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.rhs()));

    if(distance < 0)
      throw errort().with_location(expr.find_source_location())
        << "Shift distance must not be negative";

    auto bits = to_bitvector_type(binary_expr.type()).get_width();

    if(distance > bits)
      throw errort().with_location(expr.find_source_location())
        << "Shift distance is too large";

    binary_expr.rhs() =
      from_integer(distance, natural_typet{})
        .with_source_location(binary_expr.rhs().source_location());
  }
  else if(expr.id() == ID_concatenation)
  {
    auto &binary_expr = to_binary_expr(expr);

    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);

    if(
      binary_expr.lhs().type().id() != ID_signedbv &&
      binary_expr.lhs().type().id() != ID_unsignedbv)
    {
      throw errort().with_location(expr.find_source_location())
        << "Concatenation operand must have word type";
    }

    if(
      binary_expr.rhs().type().id() != ID_signedbv &&
      binary_expr.rhs().type().id() != ID_unsignedbv)
    {
      throw errort().with_location(expr.find_source_location())
        << "Concatenation operand must have word type";
    }

    auto bits = to_bitvector_type(binary_expr.lhs().type()).get_width() +
                to_bitvector_type(binary_expr.rhs().type()).get_width();

    binary_expr.type() = unsignedbv_typet{bits};
  }
  else if(expr.id() == ID_smv_sizeof)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() == ID_signedbv || op.type().id() == ID_unsignedbv)
    {
      auto bits = to_bitvector_type(op.type()).get_width();
      expr = from_integer(bits, range_typet{bits, bits});
    }
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "sizeof operand must have word type";
    }
  }
  else if(expr.id() == ID_smv_resize)
  {
    auto &binary_expr = to_binary_expr(expr);
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    PRECONDITION(binary_expr.rhs().is_constant());
    auto &lhs_type = binary_expr.lhs().type();
    auto new_bits =
      numeric_cast_v<mp_integer>(to_constant_expr(binary_expr.rhs()));

    if(lhs_type.id() == ID_signedbv)
      expr.type() = signedbv_typet{new_bits};
    else if(lhs_type.id() == ID_unsignedbv)
      expr.type() = unsignedbv_typet{new_bits};
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "resize operand must have word type";
    }
  }
  else if(expr.id() == ID_smv_extend)
  {
    auto &binary_expr = to_binary_expr(expr);
    typecheck_expr_rec(binary_expr.lhs(), mode, next);
    typecheck_expr_rec(binary_expr.rhs(), mode, next);
    PRECONDITION(binary_expr.rhs().is_constant());
    auto &lhs_type = binary_expr.lhs().type();
    auto old_bits = to_bitvector_type(lhs_type).get_width();
    auto new_bits = old_bits + numeric_cast_v<mp_integer>(
                                 to_constant_expr(binary_expr.rhs()));

    if(lhs_type.id() == ID_signedbv)
      expr.type() = signedbv_typet{new_bits};
    else if(lhs_type.id() == ID_unsignedbv)
      expr.type() = unsignedbv_typet{new_bits};
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "extend operand must have word type";
    }
  }
  else if(expr.id() == ID_smv_unsigned_cast)
  {
    // a reinterpret cast
    auto &op = to_smv_unsigned_cast_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() == ID_signedbv)
      expr.type() = unsignedbv_typet{to_signedbv_type(op.type()).get_width()};
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "unsigned operand must have signed word type";
    }
  }
  else if(expr.id() == ID_smv_signed_cast)
  {
    // a reinterpret cast
    auto &op = to_smv_signed_cast_expr(expr).op();
    typecheck_expr_rec(op, mode, next);
    if(op.type().id() == ID_unsignedbv)
      expr.type() = signedbv_typet{to_unsignedbv_type(op.type()).get_width()};
    else
    {
      throw errort().with_location(expr.find_source_location())
        << "signed operand must have unsigned word type";
    }
  }
  else if(expr.id() == ID_smv_set)
  {
    // a set literal
    expr.type() = typet{ID_smv_set};

    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode, next);
  }
  else
  {
    throw errort().with_location(expr.find_source_location())
      << "No type checking for " << expr.id();
  }
}

/*******************************************************************\

Function: smv_typecheckt::lower_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::lower_node(exprt &expr) const
{
  if(expr.id() == ID_smv_abs)
  {
    // turn into if
    auto &op = to_smv_abs_expr(expr).op();
    PRECONDITION(op.type().id() == ID_range);
    auto &range_type = to_range_type(op.type());
    if(range_type.get_from() >= 0)
      expr = op; // no change
    else if(range_type.get_to() < 0)
    {
      // always negative
      expr = unary_minus_exprt{op, expr.type()};
    }
    else
    {
      expr = if_exprt{
        binary_relation_exprt{op, ID_ge, from_integer(0, op.type())},
        typecast_exprt{op, expr.type()},
        unary_minus_exprt{op, expr.type()},
        expr.type()};
    }
  }
  else if(expr.id() == ID_smv_bool)
  {
    // turn into equality
    auto &op = to_smv_bool_expr(expr).op();
    if(op.type().id() == ID_bool)
      expr = op;
    else if(op.type().id() == ID_range)
    {
      auto &range = to_range_type(op.type());
      if(range.includes(0))
        expr = notequal_exprt{op, to_range_type(op.type()).zero_expr()};
      else
        expr = true_exprt{};
    }
    else if(op.type().id() == ID_unsignedbv)
    {
      expr = notequal_exprt{op, to_unsignedbv_type(op.type()).zero_expr()};
    }
    else
      PRECONDITION(false);
  }
  else if(expr.id() == ID_smv_count)
  {
    // turn into sum
    exprt::operandst addends;

    addends.reserve(expr.operands().size());
    auto zero = from_integer(0, expr.type());
    auto one = from_integer(1, expr.type());

    for(auto &op : expr.operands())
      addends.push_back(if_exprt{op, one, zero});

    expr = plus_exprt{std::move(addends), expr.type()};
  }
  else if(expr.id() == ID_smv_extend)
  {
    auto &smv_extend = to_smv_extend_expr(expr);
    expr = typecast_exprt{smv_extend.lhs(), smv_extend.type()};
  }
  else if(expr.id() == ID_smv_max)
  {
    // turn into if
    auto &max_expr = to_smv_max_expr(expr);
    expr = if_exprt{
      binary_relation_exprt{max_expr.lhs(), ID_ge, max_expr.rhs()},
      max_expr.lhs(),
      max_expr.rhs(),
      max_expr.type()};
  }
  else if(expr.id() == ID_smv_min)
  {
    // turn into if
    auto &min_expr = to_smv_min_expr(expr);
    expr = if_exprt{
      binary_relation_exprt{min_expr.lhs(), ID_le, min_expr.rhs()},
      min_expr.lhs(),
      min_expr.rhs(),
      min_expr.type()};
  }
  else if(expr.id() == ID_smv_resize)
  {
    auto &smv_resize = to_smv_resize_expr(expr);
    expr = typecast_exprt{smv_resize.lhs(), smv_resize.type()};
  }
  else if(expr.id() == ID_smv_signed_cast)
  {
    expr = typecast_exprt{to_smv_signed_cast_expr(expr).op(), expr.type()};
  }
  else if(expr.id() == ID_smv_unsigned_cast)
  {
    expr = typecast_exprt{to_smv_unsigned_cast_expr(expr).op(), expr.type()};
  }
  else if(expr.id() == ID_smv_setin)
  {
    auto &lhs = to_binary_expr(expr).lhs();
    auto &rhs = to_binary_expr(expr).rhs();
    if(rhs.type().id() == ID_smv_set)
    {
      DATA_INVARIANT(
        rhs.id() == ID_smv_set, "rhs of in must be set expression");
      // this is an 'or'
      exprt::operandst disjuncts;
      disjuncts.reserve(rhs.operands().size());
      for(auto &op : rhs.operands())
      {
        DATA_INVARIANT(
          lhs.type() == op.type(), "lhs/rhs of in must have same type");
        disjuncts.push_back(equal_exprt{lhs, op});
      }
      expr = disjunction(std::move(disjuncts));
    }
    else
    {
      // RHS is a singleton; this is equality
      expr.id(ID_equal);
      DATA_INVARIANT(
        lhs.type() == rhs.type(), "lhs/rhs of in must have same type");
    }
  }
  else if(expr.id() == ID_smv_toint)
  {
    auto &op = to_smv_toint_expr(expr).op();
    expr = typecast_exprt{op, expr.type()};
  }
  else if(expr.id() == ID_smv_word1)
  {
    auto &op = to_smv_word1_expr(expr).op();
    auto zero = from_integer(0, expr.type());
    auto one = from_integer(1, expr.type());
    expr = if_exprt{op, std::move(one), std::move(zero)};
  }
  else if(expr.id() == ID_smv_bitimplies)
  {
    // we'll lower a->b to !a|b
    auto &implies = to_smv_bitimplies_expr(expr);
    expr = bitor_exprt{bitnot_exprt{implies.op0()}, implies.op1()};
  }
  else if(expr.id() == ID_smv_bit_selection)
  {
    // we'll lower to extractbits
    auto &bit_selection = to_ternary_expr(expr);
    expr = extractbits_exprt{
      bit_selection.op0(), bit_selection.op2(), bit_selection.type()};
  }

  // lower the type
  lower(expr.type());
}

/*******************************************************************\

Function: smv_typecheckt::lower

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::lower(typet &type) const
{
  // lower the type
  if(type.id() == ID_smv_enumeration)
  {
    type.id(ID_enumeration);
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert_expr_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert_expr_to(exprt &expr, const typet &dest_type)
{
  const auto &src_type = expr.type();

  PRECONDITION(dest_type.is_not_nil());

  if(src_type != dest_type)
  {
    if(src_type.id() == ID_smv_set && expr.id() == ID_smv_set)
    {
      // sets can be assigned to scalars, which yields a nondeterministic
      // choice
      std::string identifier =
        module + "::var::" + std::to_string(nondet_count++);

      expr.set(ID_identifier, identifier);
      expr.set("#smv_nondet_choice", true);

      expr.id(ID_constraint_select_one);
      expr.type() = dest_type;

      // apply recursively
      for(auto &op : expr.operands())
        convert_expr_to(op, dest_type);

      return;
    }

    if(dest_type.id() == ID_signedbv || dest_type.id() == ID_unsignedbv)
    {
      // no implicit conversion
    }
    else if(dest_type.id() == ID_range)
    {
      if(src_type.id() == ID_range)
      {
        // range to range
        if(expr.id() == ID_constant)
        {
          // re-type the constant
          auto value = numeric_cast_v<mp_integer>(to_constant_expr(expr));
          if(to_range_type(dest_type).includes(value))
          {
            expr = from_integer(value, dest_type);
            return;
          }
        }
        else if(expr.id() == ID_cond)
        {
          // re-type the cond
          bool condition = true;

          for(auto &op : expr.operands())
          {
            if(!condition)
              convert_expr_to(op, dest_type);

            condition = !condition;
          }
          expr.type() = dest_type;
          return;
        }
        else
        {
          expr = typecast_exprt{expr, dest_type};
          return;
        }
      }
      else if(src_type.id() == ID_integer)
      {
        // integer to range
        if(expr.id() == ID_constant)
        {
          // re-type the constant
          auto value = numeric_cast_v<mp_integer>(to_constant_expr(expr));
          if(to_range_type(dest_type).includes(value))
          {
            expr = from_integer(value, dest_type);
            return;
          }
        }
      }
    }
    else if(dest_type.id() == ID_bool)
    {
      // legacy -- convert 0/1 to false/true
      if(src_type.id() == ID_range)
      {
        auto &range_type = to_range_type(src_type);
        if(range_type.get_from() == 0 && range_type.get_to() == 0)
        {
          expr = false_exprt{};
          return;
        }
        else if(range_type.get_from() == 1 && range_type.get_to() == 1)
        {
          expr = true_exprt{};
          return;
        }
      }
    }
    else if(dest_type.id() == ID_smv_enumeration)
    {
      auto &dest_e_type = to_smv_enumeration_type(dest_type);

      if(expr.type().id() == ID_smv_enumeration)
      {
        // subset?
        if(to_smv_enumeration_type(expr.type()).is_subset_of(dest_e_type))
        {
          // yes, it's a subset
          if(expr.is_constant())
          {
            // re-type the constant
            expr.type() = dest_type;
            return;
          }
          else if(expr.id() == ID_typecast)
          {
            // created by type unions
            auto &op = to_typecast_expr(expr).op();
            if(
              expr.type().id() == ID_smv_enumeration &&
              op.type().id() == ID_smv_enumeration)
            {
              convert_expr_to(op, dest_type);
              expr = std::move(op);
              return;
            }
          }
          else // anything else
          {
            expr = typecast_exprt{std::move(expr), dest_type};
            return;
          }
        }
      }
    }

    throw errort().with_location(expr.find_source_location())
      << "Expected expression of type `" << to_string(dest_type)
      << "', but got expression `" << to_string(expr) << "', which is of type `"
      << to_string(src_type) << "'";
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(exprt &expr)
{
  for(auto &op : expr.operands())
    convert(op);

  if(expr.id() == ID_smv_identifier)
  {
    const std::string &identifier=expr.get_string(ID_identifier);

    DATA_INVARIANT(
      identifier.find("::") == std::string::npos, "conversion is done once");

    // enum or variable?
    if(
      smv_parse_tree.enum_set.find(identifier) == smv_parse_tree.enum_set.end())
    {
      std::string id = module + "::var::" + identifier;

      expr.set(ID_identifier, id);
      expr.id(ID_symbol);
    }
    else
    {
      expr.id(ID_constant);
      expr.type() = typet(ID_smv_enumeration);
      expr.set(ID_value, identifier);
      expr.remove(ID_identifier);
    }
  }
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      member_expr.compound().id() == ID_symbol,
      "unexpected complex_identifier",
      expr.pretty());

    auto tmp = to_symbol_expr(member_expr.compound());
    tmp.set_identifier(
      id2string(tmp.get_identifier()) + '.' +
      id2string(member_expr.get_component_name()));
    expr = tmp;
  }
  else if(expr.id() == ID_index)
  {
    auto &index_expr = to_index_expr(expr);
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      index_expr.array().id() == ID_symbol,
      "unexpected complex_identifier",
      expr.pretty());
    auto &index = index_expr.index();
    PRECONDITION(index.is_constant());
    auto index_string = id2string(to_constant_expr(index).get_value());
    auto tmp = to_symbol_expr(index_expr.array());
    tmp.set_identifier(id2string(tmp.get_identifier()) + '.' + index_string);
    expr = tmp;
  }
  else if(expr.id()=="smv_nondet_choice" ||
          expr.id()=="smv_union")
  {
    if(expr.operands().size()==0)
    {
      throw errort().with_location(expr.find_source_location())
        << "expected operand here";
    }

    std::string identifier=
      module+"::var::"+std::to_string(nondet_count++);

    expr.set(ID_identifier, identifier);
    expr.set("#smv_nondet_choice", true);

    expr.id(ID_constraint_select_one);
  }
  else if(expr.id() == ID_smv_cases) // cases
  {
    if(expr.operands().size()<1)
    {
      throw errort().with_location(expr.find_source_location())
        << "Expected at least one operand for " << expr.id() << " expression";
    }

    exprt tmp;
    tmp.operands().swap(expr.operands());
    expr.reserve_operands(tmp.operands().size()*2);

    for(auto &op : tmp.operands())
    {
      if(op.operands().size() != 2)
      {
        throw errort().with_location(op.find_source_location())
          << "case expected to have two operands";
      }

      exprt &condition = to_binary_expr(op).op0();
      exprt &value = to_binary_expr(op).op1();

      expr.add_to_operands(std::move(condition));
      expr.add_to_operands(std::move(value));
    }

    expr.id(ID_cond);
  }
}

/*******************************************************************\

Function: smv_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smv_typecheckt::to_string(const exprt &expr)
{
  namespacet ns{symbol_table};
  return expr2smv(expr, ns);
}

/*******************************************************************\

Function: smv_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smv_typecheckt::to_string(const typet &type)
{
  namespacet ns{symbol_table};
  return type2smv(type, ns);
}

/*******************************************************************\

Function: smv_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck(smv_parse_treet::modulet::elementt &element)
{
  switch(element.element_type)
  {
  case smv_parse_treet::modulet::elementt::INIT:
    typecheck(element.expr, INIT);
    convert_expr_to(element.expr, bool_typet{});
    no_next_allowed(element.expr);
    return;

  case smv_parse_treet::modulet::elementt::TRANS:
    typecheck(element.expr, TRANS);
    convert_expr_to(element.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::elementt::CTLSPEC:
    typecheck(element.expr, CTL);
    convert_expr_to(element.expr, bool_typet{});
    no_next_allowed(element.expr);
    return;

  case smv_parse_treet::modulet::elementt::LTLSPEC:
    typecheck(element.expr, LTL);
    convert_expr_to(element.expr, bool_typet{});
    no_next_allowed(element.expr);
    return;

  case smv_parse_treet::modulet::elementt::INVAR:
    typecheck(element.expr, INVAR);
    convert_expr_to(element.expr, bool_typet{});
    no_next_allowed(element.expr);
    return;

  case smv_parse_treet::modulet::elementt::FAIRNESS:
    typecheck(element.expr, OTHER);
    convert_expr_to(element.expr, bool_typet{});
    no_next_allowed(element.expr);
    return;

  case smv_parse_treet::modulet::elementt::ASSIGN_CURRENT:
    typecheck(element.lhs(), OTHER);
    typecheck(element.rhs(), OTHER);
    convert_expr_to(element.rhs(), element.lhs().type());
    element.expr.type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::elementt::ASSIGN_INIT:
    typecheck(element.lhs(), INIT);
    typecheck(element.rhs(), INIT);
    convert_expr_to(element.rhs(), element.lhs().type());
    no_next_allowed(element.rhs());
    element.expr.type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::elementt::ASSIGN_NEXT:
    typecheck(element.lhs(), TRANS);
    typecheck(element.rhs(), TRANS);
    convert_expr_to(element.rhs(), element.lhs().type());
    element.expr.type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::elementt::DEFINE:
    typecheck(element.expr, OTHER);
    element.expr.type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::elementt::ENUM:
  case smv_parse_treet::modulet::elementt::IVAR:
  case smv_parse_treet::modulet::elementt::VAR:
    return;
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(smv_parse_treet::modulet::elementt &element)
{
  convert(element.expr);
}

/*******************************************************************\

Function: smv_typecheckt::variable_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::variable_checks(const smv_parse_treet::modulet &module)
{
  std::unordered_set<irep_idt, irep_id_hash> enums, defines, vars, parameters;

  for(const auto &parameter : module.parameters)
    parameters.insert(parameter);

  for(const auto &element : module.elements)
  {
    if(element.is_var() || element.is_ivar())
    {
      irep_idt base_name = merge_complex_identifier(element.expr);
      auto location = element.expr.source_location();

      // already used as enum?
      if(enums.find(base_name) != enums.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as enum";
      }

      // already used as a parameter?
      if(parameters.find(base_name) != parameters.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as a parameter";
      }

      // already used as variable?
      if(vars.find(base_name) != vars.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as variable";
      }

      // already used as define?
      if(defines.find(base_name) != defines.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as define";
      }

      vars.insert(base_name);
    }
    else if(element.is_define())
    {
      irep_idt base_name = merge_complex_identifier(element.lhs());
      auto location = to_equal_expr(element.expr).lhs().source_location();

      // already used as enum?
      if(enums.find(base_name) != enums.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as enum";
      }

      // already used as a parameter?
      if(parameters.find(base_name) != parameters.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as a parameter";
      }

      // already used as variable?
      if(vars.find(base_name) != vars.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as variable";
      }

      // already used as define?
      if(defines.find(base_name) != defines.end())
      {
        throw errort{}.with_location(location)
          << "identifier " << base_name << " already used as define";
      }

      defines.insert(base_name);
    }
    else if(element.is_enum())
    {
      const auto &identifier_expr = to_smv_identifier_expr(element.expr);
      irep_idt base_name = identifier_expr.identifier();

      // already used as a parameter?
      if(parameters.find(base_name) != parameters.end())
      {
        throw errort{}.with_location(identifier_expr.source_location())
          << "identifier " << base_name << " already used as a parameter";
      }

      // already used as variable?
      if(vars.find(base_name) != vars.end())
      {
        throw errort{}.with_location(identifier_expr.source_location())
          << "identifier " << base_name << " already used as variable";
      }

      // already used as define?
      if(defines.find(base_name) != defines.end())
      {
        throw errort{}.with_location(identifier_expr.source_location())
          << "identifier " << base_name << " already used as define";
      }

      enums.insert(base_name);
    }
  }
}

/*******************************************************************\

Function: smv_typecheckt::create_var_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::create_var_symbols(
  const smv_parse_treet::modulet::element_listt &elements)
{
  const irep_idt mode = "SMV";

  for(const auto &element : elements)
  {
    if(element.is_var() || element.is_ivar())
    {
      irep_idt base_name = merge_complex_identifier(element.expr);
      auto location = element.expr.source_location();
      irep_idt identifier = module + "::var::" + id2string(base_name);

      auto symbol_ptr = symbol_table.lookup(identifier);
      if(symbol_ptr != nullptr)
      {
        throw errort{}.with_location(location)
          << "variable " << base_name << " already declared, at "
          << symbol_ptr->location;
      }

      typet type = element.expr.type();

      // check the type
      check_type(type);

      symbolt symbol{identifier, std::move(type), mode};

      symbol.module = modulep->name;
      symbol.base_name = base_name;

      if(module == "smv::main")
        symbol.pretty_name = symbol.base_name;
      else
        symbol.pretty_name = strip_smv_prefix(symbol.name);

      if(symbol.type.id() == ID_smv_module_instance)
        symbol.is_input = false;
      else
        symbol.is_input = true;

      symbol.is_state_var = false;
      symbol.value = nil_exprt{};
      symbol.location = location;

      symbol_table.insert(std::move(symbol));
    }
    else if(element.is_define())
    {
      irep_idt base_name = merge_complex_identifier(element.lhs());
      auto location = to_equal_expr(element.expr).lhs().source_location();
      irep_idt identifier = module + "::var::" + id2string(base_name);

      auto symbol_ptr = symbol_table.lookup(identifier);
      if(symbol_ptr != nullptr)
      {
        throw errort{}.with_location(location)
          << "variable `" << base_name << "' already declared, at "
          << symbol_ptr->location;
      }

      typet type;
      type.make_nil();

      symbolt symbol{identifier, std::move(type), mode};

      symbol.mode = mode;
      symbol.module = modulep->name;
      symbol.base_name = base_name;

      if(module == "smv::main")
        symbol.pretty_name = symbol.base_name;
      else
        symbol.pretty_name = strip_smv_prefix(symbol.name);

      symbol.value = nil_exprt{};
      symbol.is_input = true;
      symbol.is_state_var = false;
      symbol.location = location;

      symbol_table.insert(std::move(symbol));
    }
    else if(element.is_enum())
    {
      irep_idt base_name = to_smv_identifier_expr(element.expr).identifier();
      irep_idt identifier = module + "::var::" + id2string(base_name);

      auto symbol_ptr = symbol_table.lookup(identifier);
      if(symbol_ptr != nullptr)
      {
        throw errort{}.with_location(element.expr.source_location())
          << "enum " << base_name << " already declared, at "
          << symbol_ptr->location;
      }
    }
  }
}

/*******************************************************************\

Function: smv_typecheckt::collect_define

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::collect_define(const exprt &lhs, const exprt &rhs)
{
  if(lhs.id() != ID_symbol)
    throw errort() << "collect_define expects symbol on left hand side";

  const irep_idt &identifier = to_symbol_expr(lhs).get_identifier();

  auto it=symbol_table.get_writeable(identifier);

  if(it==nullptr)
  {
    throw errort() << "collect_define failed to find symbol `" << identifier
                   << "'";
  }

  symbolt &symbol=*it;

  symbol.value.make_nil();
  symbol.is_input=false;
  symbol.is_state_var=false;
  symbol.is_macro=false;

  std::pair<define_mapt::iterator, bool> result =
    define_map.insert(std::pair<irep_idt, definet>{identifier, definet{rhs}});

  if(!result.second)
  {
    throw errort().with_location(lhs.source_location())
      << "variable `" << symbol.display_name() << "' already defined";
  }
}

/*******************************************************************\

Function: smv_typecheckt::uses_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_typecheckt::uses_next(const exprt &expr) const
{
  if(expr.id() == ID_next_symbol)
    return true;

  if(expr.id() == ID_symbol)
  {
    auto d_it = define_map.find(to_symbol_expr(expr).get_identifier());
    if(d_it != define_map.end())
      return d_it->second.uses_next;
  }

  for(auto &op : expr.operands())
    if(uses_next(op))
      return true;

  return false;
}

/*******************************************************************\

Function: smv_typecheckt::no_next_allowed

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::no_next_allowed(const exprt &expr) const
{
  if(uses_next(expr))
    throw errort().with_location(expr.find_source_location())
      << "next(...) is not allowed here";
}

/*******************************************************************\

Function: smv_typecheckt::convert_define

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert_define(const irep_idt &identifier)
{
  definet &d=define_map[identifier];
  
  if(d.typechecked) return;
  
  if(d.in_progress)
  {
    throw errort() << "definition of `" << identifier << "' is cyclic";
  }
  
  auto it=symbol_table.get_writeable(identifier);

  if(it==nullptr)
  {
    throw errort() << "convert_define failed to find symbol `" << identifier
                   << "'";
  }

  symbolt &symbol=*it;

  d.in_progress=true;

  typecheck(d.value, OTHER);

  if(symbol.type.is_not_nil())
    convert_expr_to(d.value, symbol.type);

  d.in_progress=false;
  d.typechecked=true;
  d.uses_next = uses_next(d.value);

  // VAR x : type; ASSIGN x := ... does come with a type.
  // DEFINE x := ... doesn't come with a type.
  if(symbol.type.is_nil())
    symbol.type=d.value.type();
}

/*******************************************************************\

Function: smv_typecheckt::convert_defines

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert_defines(exprt::operandst &invar)
{
  for(auto &define_it : define_map)
  {
    convert_define(define_it.first);

    // generate constraint
    equal_exprt equality{
      symbol_exprt{define_it.first, define_it.second.value.type()},
      define_it.second.value};
    invar.push_back(equality);
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(smv_parse_treet::modulet &smv_module)
{
  modulep=&smv_module;

  define_map.clear();

  // expand the module hierarchy
  flatten_hierarchy(smv_module);

  // Now do variables/defines, which can be used before their declaration
  create_var_symbols(smv_module.elements);

  // transition relation

  {
    symbolt module_symbol;

    module_symbol.base_name=smv_module.base_name;
    module_symbol.pretty_name=smv_module.base_name;
    module_symbol.name=smv_module.name;
    module_symbol.module=module_symbol.name;
    module_symbol.type=typet(ID_module);
    module_symbol.mode="SMV";

    exprt::operandst trans_invar, trans_init, trans_trans;

    convert_ports(smv_module, module_symbol.type);

    // non-variable elements
    for(auto &element : smv_module.elements)
      if(!element.is_var() && !element.is_ivar())
        convert(element);

    // we first need to collect all the defines

    for(auto &element : smv_module.elements)
    {
      if(element.is_define() || element.is_assign_current())
        collect_define(element.lhs(), element.rhs());
    }
    // now turn them into INVARs
    convert_defines(trans_invar);

    // do the rest now: typecheck
    for(auto &element : smv_module.elements)
    {
      if(!element.is_define() && !element.is_assign_current())
        typecheck(element);
    }

    // copy to transition system
    for(const auto &element : smv_module.elements)
    {
      if(element.is_invar())
        trans_invar.push_back(element.expr);
      else if(element.is_init())
        trans_init.push_back(element.expr);
      else if(element.is_assign_init())
        trans_init.push_back(element.expr);
      else if(element.is_assign_next())
        trans_trans.push_back(element.expr);
      else if(element.is_trans())
        trans_trans.push_back(element.expr);
    }

    module_symbol.value =
        transt{ID_trans, conjunction(trans_invar), conjunction(trans_init),
               conjunction(trans_trans), module_symbol.type};

    module_symbol.pretty_name = strip_smv_prefix(module_symbol.name);

    symbol_table.add(module_symbol);
  }

  // spec

  if(do_spec)
  {
    unsigned nr=1;

    for(auto &element : smv_module.elements)
    {
      if(element.is_ctlspec() || element.is_ltlspec())
      {
        symbolt spec_symbol;

        if(element.name.has_value())
          spec_symbol.base_name = element.name.value();
        else
          spec_symbol.base_name = "spec" + std::to_string(nr++);

        spec_symbol.name =
          id2string(smv_module.name) + "::" + id2string(spec_symbol.base_name);
        spec_symbol.module = smv_module.name;
        spec_symbol.type = bool_typet();
        spec_symbol.is_property = true;
        spec_symbol.mode = "SMV";
        spec_symbol.value = element.expr;
        spec_symbol.location = element.location;
        spec_symbol.location.set_comment(to_string(element.expr));

        if(smv_module.name == "smv::main")
          spec_symbol.pretty_name = spec_symbol.base_name;
        else
          spec_symbol.pretty_name = strip_smv_prefix(spec_symbol.name);

        // lowering

        symbol_table.add(spec_symbol);
      }
    }
  }

  // lowering
  for(auto v_it = symbol_table.symbol_module_map.lower_bound(smv_module.name);
      v_it != symbol_table.symbol_module_map.upper_bound(smv_module.name);
      v_it++)
  {
    auto &symbol = symbol_table.get_writeable_ref(v_it->second);
    lower(symbol.type);
    lower(symbol.value);
  }
}

/*******************************************************************\

Function: smv_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck()
{
  if(module != "smv::main")
    return;

  // check all modules for duplicate identifiers
  for(auto &module : smv_parse_tree.module_list)
    variable_checks(module);

  auto it = smv_parse_tree.module_map.find(module);

  if(it == smv_parse_tree.module_map.end())
  {
    throw errort() << "failed to find module " << module;
  }

  convert(*it->second);
}

/*******************************************************************\

Function: smv_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_typecheck(
  smv_parse_treet &smv_parse_tree,
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler,
  bool do_spec)
{
  smv_typecheckt smv_typecheck(
    smv_parse_tree, symbol_table, module, do_spec, message_handler);
  return smv_typecheck.typecheck_main();
}

/*******************************************************************\

Function: smv_module_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smv_module_symbol(const std::string &module)
{
  return "smv::"+module;
}
