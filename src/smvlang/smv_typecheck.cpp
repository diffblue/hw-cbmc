/*******************************************************************\

Module: SMV Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_typecheck.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/typecheck.h>

#include "expr2smv.h"
#include "smv_range.h"

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
    TRANS,
    OTHER,
    LTL,
    CTL
  } modet;

  void convert(smv_parse_treet::modulet &);
  void convert(smv_parse_treet::mc_varst &);

  void collect_define(const equal_exprt &);
  void convert_defines(exprt::operandst &invar);
  void convert_define(const irep_idt &identifier);

  typedef enum { NORMAL, NEXT } expr_modet;
  void convert(exprt &, expr_modet);

  void typecheck(exprt &, const typet &, modet);
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

  void check_type(const typet &);
  smv_ranget convert_type(const typet &);
  static bool is_contained_in(irep_idt, const enumeration_typet &);

  void convert(smv_parse_treet::modulet::itemt &);
  void typecheck(smv_parse_treet::modulet::itemt &);
  void typecheck_expr_rec(exprt &, const typet &, modet);
  void typecheck_expr_rec(exprt &, modet);
  void convert_expr_to(exprt &, const typet &dest);

  smv_parse_treet::modulet *modulep;

  unsigned nondet_count;

  void flatten_hierarchy(smv_parse_treet::modulet &);

  void instantiate(
    smv_parse_treet::modulet &,
    const irep_idt &identifier,
    const irep_idt &instance,
    const exprt::operandst &operands,
    const source_locationt &);
    
  typet type_union(
    const typet &type1,
    const typet &type2);

  typedef std::map<irep_idt, exprt> rename_mapt;

  void instantiate_rename(exprt &, const rename_mapt &rename_map);

  void convert_ports(smv_parse_treet::modulet &, typet &dest);

  // for defines
  class definet
  {
  public:
    exprt value;
    bool typechecked, in_progress;
    
    explicit definet(const exprt &_v):value(_v), typechecked(false), in_progress(false)
    {
    }

    definet():typechecked(false), in_progress(false)
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
};

/*******************************************************************\

Function: smv_typecheckt::is_contained_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_typecheckt::is_contained_in(irep_idt id, const enumeration_typet &type)
{
  for(auto &element : type.elements())
    if(element.id() == id)
      return true;
  return false;
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

  ports.reserve(smv_module.ports.size());

  for(const auto &port_name : smv_module.ports)
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
  for(auto &var_it : smv_module.vars)
  {
    smv_parse_treet::mc_vart &var = var_it.second;

    if(var.type.id()=="submodule")
    {
      exprt &inst=static_cast<exprt &>(static_cast<irept &>(var.type));

      for(auto &op : inst.operands())
        convert(op, NORMAL);

      instantiate(
        smv_module,
        inst.get(ID_identifier),
        var_it.first,
        inst.operands(),
        inst.find_source_location());
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
  const exprt::operandst &operands,
  const source_locationt &location)
{
  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);

  if(s_it==symbol_table.symbols.end())
  {
    throw errort().with_location(location)
      << "submodule `" << identifier << "' not found";
  }

  if(s_it->second.type.id()!=ID_module)
  {
    throw errort().with_location(location)
      << "submodule `" << identifier << "' not a module";
  }

  const irept::subt &ports=s_it->second.type.find(ID_ports).get_sub();

  // do the arguments/ports

  if(ports.size()!=operands.size())
  {
    throw errort().with_location(location)
      << "submodule `" << identifier << "' has wrong number of arguments";
  }

  std::set<irep_idt> port_identifiers;
  rename_mapt rename_map;

  for(std::size_t i = 0; i < ports.size(); i++)
  {
    const irep_idt &identifier=ports[i].get(ID_identifier);
    rename_map.insert(std::pair<irep_idt, exprt>(identifier, operands[i]));
    port_identifiers.insert(identifier);
  }

  // do the variables

  std::string new_prefix=
    id2string(smv_module.name)+"::var::"+id2string(instance)+".";

  std::set<irep_idt> var_identifiers;

  for(auto v_it=symbol_table.symbol_module_map.lower_bound(identifier);
      v_it!=symbol_table.symbol_module_map.upper_bound(identifier);
      v_it++)
  {
    symbol_table_baset::symbolst::const_iterator s_it2 =
      symbol_table.symbols.find(v_it->second);

    if(s_it2==symbol_table.symbols.end())
    {
      throw errort() << "symbol `" << v_it->second << "' not found";
    }

    if(port_identifiers.find(s_it2->first) != port_identifiers.end())
    {
    }
    else if(s_it2->second.type.id() == ID_module)
    {
    }
    else
    {
      symbolt symbol(s_it2->second);

      symbol.name=new_prefix+id2string(symbol.base_name);
      symbol.module=smv_module.name;

      if(smv_module.name == "smv::main")
      {
        symbol.pretty_name =
          id2string(instance) + '.' + id2string(symbol.base_name);
      }
      else
      {
        symbol.pretty_name = strip_smv_prefix(symbol.name);
      }

      rename_map.insert(
          std::pair<irep_idt, exprt>(s_it2->first, symbol.symbol_expr()));

      var_identifiers.insert(symbol.name);

      symbol_table.add(symbol);
    }
  }

  // fix values (macros)

  for(const auto &v_id : var_identifiers)
  {
    auto s_it2 = symbol_table.get_writeable(v_id);

    if(s_it2==nullptr)
    {
      throw errort() << "symbol `" << v_id << "' not found";
    }

    symbolt &symbol=*s_it2;

    if(!symbol.value.is_nil())
    {
      instantiate_rename(symbol.value, rename_map);
      typecheck(symbol.value, symbol.type, OTHER);
    }
  }

  // get the transition system

  const transt &trans=to_trans_expr(s_it->second.value);

  std::string old_prefix=id2string(s_it->first)+"::var::";

  // do the transition system

  if(!trans.invar().is_true())
  {
    exprt tmp(trans.invar());
    instantiate_rename(tmp, rename_map);
    smv_module.add_invar(tmp);
  }
    
  if(!trans.init().is_true())
  {
    exprt tmp(trans.init());
    instantiate_rename(tmp, rename_map);
    smv_module.add_init(tmp);
  }
    
  if(!trans.trans().is_true())
  {
    exprt tmp(trans.trans());
    instantiate_rename(tmp, rename_map);
    smv_module.add_trans(tmp);
  }

}

/*******************************************************************\

Function: smv_typecheckt::instantiate_rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::instantiate_rename(
  exprt &expr,
  const rename_mapt &rename_map)
{
  for(auto &op : expr.operands())
    instantiate_rename(op, rename_map);

  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    const irep_idt &old_identifier=expr.get(ID_identifier);
    bool next=expr.id()==ID_next_symbol;

    rename_mapt::const_iterator it=
      rename_map.find(old_identifier);

    if(it!=rename_map.end())
    {
      expr=it->second;

      if(next)
      {
        if(expr.id()==ID_symbol)
        {
          expr=it->second;
          expr.id(ID_next_symbol);
        }
        else
        {
          throw errort().with_location(expr.find_source_location())
            << "expected symbol expression here, but got "
            << to_string(it->second);
        }
      }
      else
        expr=it->second;
    }
  }
}

/*******************************************************************\

Function: smv_typecheckt::typecheck_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck_op(
  exprt &expr,
  const typet &type,
  modet mode)
{
  if(expr.operands().size()==0)
  {
    throw errort().with_location(expr.find_source_location())
      << "Expected operands for " << expr.id() << " operator";
  }

  for(auto &op : expr.operands())
    typecheck_expr_rec(op, type, mode);

  expr.type()=type;

  // type fixed?

  if(type.is_nil())
  {
    // figure out types

    for(const auto &op : expr.operands())
      if(!op.type().is_nil())
      {
        expr.type() = op.type();
        break;
      }
  }
}

/*******************************************************************\

Function: smv_typecheckt::check_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::check_type(const typet &type)
{
  if(type.id() == ID_range)
  {
    auto range = smv_ranget::from_type(to_range_type(type));

    if(range.from > range.to)
      throw errort().with_location(type.source_location()) << "range is empty";
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
  else if(src.id()==ID_enumeration)
  {
    smv_ranget dest;

    dest.from=0;

    std::size_t number_of_elements=
      to_enumeration_type(src).elements().size();
      
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
  const typet &type2)
{
  if(type1==type2) return type1;

  if(type1.is_nil())
    return type2;

  if(type2.is_nil())
    return type1;
    
  // both enums?
  if(type1.id()==ID_enumeration && type2.id()==ID_enumeration)
  {
    if(to_enumeration_type(type2).elements().empty())
      return type1;
  
    if(to_enumeration_type(type1).elements().empty())
      return type2;
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

void smv_typecheckt::typecheck(
  exprt &expr,
  const typet &type,
  modet mode)
{
  typecheck_expr_rec(expr, type, mode);
}

/*******************************************************************\

Function: smv_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck(exprt &expr, modet mode)
{
  typecheck_expr_rec(expr, static_cast<const typet &>(get_nil_irep()), mode);
}

/*******************************************************************\

Function: smv_typecheckt::typecheck_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck_expr_rec(exprt &expr, modet mode)
{
  typecheck_expr_rec(expr, static_cast<const typet &>(get_nil_irep()), mode);
}

/*******************************************************************\

Function: smv_typecheckt::typecheck_expr_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck_expr_rec(
  exprt &expr,
  const typet &dest_type,
  modet mode)
{
  const auto static nil_type = static_cast<const typet &>(get_nil_irep());

  if(expr.id()==ID_symbol || 
     expr.id()==ID_next_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    bool next=expr.id()==ID_next_symbol;
    
    if(define_map.find(identifier)!=define_map.end())
      convert_define(identifier);

    auto s_it=symbol_table.get_writeable(identifier);

    if(s_it==nullptr)
    {
      throw errort().with_location(expr.find_source_location())
        << "variable `" << identifier << "' not found";
    }

    symbolt &symbol=*s_it;
    
    assert(symbol.type.is_not_nil());
    expr.type()=symbol.type;

    if(mode==INIT || (mode==TRANS && next))
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
    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode);

    expr.type() = bool_typet{};

    for(auto &op : expr.operands())
      convert_expr_to(op, expr.type());
  }
  else if(expr.id() == ID_smv_iff)
  {
    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode);

    expr.type() = bool_typet{};

    for(auto &op : expr.operands())
      convert_expr_to(op, expr.type());

    expr.set(ID_C_smv_iff, true);
    expr.id(ID_equal);
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    typecheck_op(expr, dest_type, mode);

    typet op_type;
    op_type.make_nil();

    for(const auto &op : expr.operands())
    {
      typet tmp = type_union(op.type(), op_type);
      op_type=tmp;
    }

    for(auto &op : expr.operands())
      typecheck_expr_rec(op, op_type, mode);

    expr.type()=op_type;
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal ||
          expr.id()==ID_lt || expr.id()==ID_le ||
          expr.id()==ID_gt || expr.id()==ID_ge)
  {
    for(auto &op : expr.operands())
      typecheck_expr_rec(op, mode);

    if(expr.operands().size()!=2)
    {
      throw errort().with_location(expr.find_source_location())
        << "Expected two operands for " << expr.id();
    }

    expr.type() = bool_typet{};

    exprt &op0 = to_binary_expr(expr).op0(), &op1 = to_binary_expr(expr).op1();

    typet op_type=type_union(op0.type(), op1.type());

    typecheck_expr_rec(op0, op_type, mode);
    typecheck_expr_rec(op1, op_type, mode);

    INVARIANT(op0.type() == op1.type(), "type of operands of relational operators");

    if(expr.id()==ID_lt || expr.id()==ID_le ||
       expr.id()==ID_gt || expr.id()==ID_ge)
    {
      if(op0.type().id()!=ID_range)
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
    typecheck_expr_rec(if_expr.cond(), mode);
    convert_expr_to(if_expr.cond(), bool_typet{});
    typecheck_expr_rec(true_case, dest_type, mode);
    typecheck_expr_rec(false_case, dest_type, mode);
    expr.type() = dest_type;
  }
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult || expr.id()==ID_div ||
          expr.id()==ID_mod)
  {
    typecheck_op(expr, dest_type, mode);

    if(expr.operands().size()!=2)
    {
      throw errort().with_location(expr.find_source_location())
        << "Expected two operands for " << expr.id();
    }

    if(dest_type.is_nil())
    {
      if(expr.type().id()==ID_range ||
         expr.type().id()==ID_bool)
      {
        // find proper type for precise arithmetic
        smv_ranget new_range;

        smv_ranget smv_range0 = convert_type(to_binary_expr(expr).op0().type());
        smv_ranget smv_range1 = convert_type(to_binary_expr(expr).op1().type());

        if(expr.id()==ID_plus)
          new_range=smv_range0+smv_range1;
        else if(expr.id()==ID_minus)
          new_range=smv_range0-smv_range1;
        else if(expr.id()==ID_mult)
          new_range=smv_range0*smv_range1;
        else if(expr.id()==ID_div)
          new_range=smv_range0;
        else if(expr.id()==ID_mod)
          new_range=smv_range1;
        else
          assert(false);

        expr.type() = new_range.to_type();
      }
    }
    else if(dest_type.id() != ID_range)
    {
      throw errort().with_location(expr.find_source_location())
        << "Expected number type for " << to_string(expr);
    }
  }
  else if(expr.id()==ID_constant)
  {
    const auto value = to_constant_expr(expr).get_value();

    if(expr.type().id()==ID_integer)
    {
      mp_integer int_value = string2integer(id2string(value));

      if(dest_type.is_nil())
      {
        expr.type() = range_typet{int_value, int_value};
      }
      else
      {
        expr.type() = dest_type;

        if(dest_type.id() == ID_bool)
        {
          if(int_value==0)
            expr=false_exprt();
          else if(int_value==1)
            expr=true_exprt();
          else
          {
            throw errort().with_location(expr.find_source_location())
              << "expected 0 or 1 here, but got " << value;
          }
        }
        else if(dest_type.id() == ID_range)
        {
          smv_ranget smv_range = convert_type(dest_type);

          if(int_value<smv_range.from || int_value>smv_range.to)
          {
            throw errort().with_location(expr.find_source_location())
              << "expected " << smv_range.from << ".." << smv_range.to
              << " here, but got " << value;
          }
        }
        else
        {
          throw errort().with_location(expr.find_source_location())
            << "Unexpected constant: " << value;
        }
      }
    }
    else if(expr.type().id()==ID_enumeration)
    {
      if(dest_type.id() == ID_enumeration)
      {
        if(!is_contained_in(value, to_enumeration_type(dest_type)))
        {
          throw errort().with_location(expr.find_source_location())
            << "enum " << value << " not a member of " << to_string(dest_type);
        }

        if(to_enumeration_type(expr.type()).elements().empty())
          expr.type() = dest_type;
      }
    }
    else if(dest_type.is_not_nil() && dest_type != expr.type())
    {
      // already done, but maybe need to change the type
      mp_integer int_value;
      bool have_int_value=false;
      
      if(expr.type().id()==ID_bool)
      {
        int_value=expr.is_true()?1:0;
        have_int_value=true;
      }
      else if(expr.type().id()==ID_range)
      {
        int_value=string2integer(expr.get_string(ID_value));
        have_int_value=true;
      }

      if(have_int_value)
      {
        if(dest_type.id() == ID_bool)
        {
          if(int_value==0)
            expr=false_exprt();
          else if(int_value==1)
            expr=true_exprt();
        }
        else if(dest_type.id() == ID_range)
        {
          mp_integer from = string2integer(dest_type.get_string(ID_from)),
                     to = string2integer(dest_type.get_string(ID_to));

          if(int_value>=from && int_value<=to)
          {
            expr = exprt(ID_constant, dest_type);
            expr.set(ID_value, integer2string(int_value));
          }
        }
      }
    }
  }
  else if(expr.id()==ID_cond)
  {
    if(dest_type.is_nil())
    {
      bool condition=true;
      
      expr.type().make_nil();

      for(auto &op : expr.operands())
      {
        if(condition)
        {
          typecheck_expr_rec(op, mode);
          convert_expr_to(op, bool_typet{});
        }
        else
        {
          typecheck_expr_rec(
            op, static_cast<const typet &>(get_nil_irep()), mode);
          expr.type() = type_union(expr.type(), op.type());
        }

        condition=!condition;
      }
    }
    else
    {
      expr.type() = dest_type;

      bool condition=true;

      for(auto &op : expr.operands())
      {
        if(condition)
        {
          typecheck_expr_rec(op, mode);
          convert_expr_to(op, bool_typet{});
        }
        else
          typecheck_expr_rec(op, expr.type(), mode);

        condition=!condition;
      }
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
    typecheck_expr_rec(op, mode);
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
    typecheck_expr_rec(op2, mode);
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
      typecheck_expr_rec(expr.operands()[i], mode);
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
    typecheck_expr_rec(op, mode);
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
    typecheck_expr_rec(binary_expr.lhs(), mode);
    typecheck_expr_rec(binary_expr.rhs(), mode);
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
    typecheck_expr_rec(binary_expr.lhs(), mode);
    typecheck_expr_rec(binary_expr.rhs(), mode);
    convert_expr_to(binary_expr.lhs(), expr.type());
    convert_expr_to(binary_expr.rhs(), expr.type());
  }
  else if(expr.id()==ID_typecast)
  {
  }
  else if(expr.id() == ID_smv_setin)
  {
    expr.type()=bool_typet();
  }
  else if(expr.id() == ID_smv_setnotin)
  {
    expr.type()=bool_typet();
  }
  else
  {
    throw errort().with_location(expr.find_source_location())
      << "No type checking for " << expr.id();
  }

  if(!dest_type.is_nil())
    convert_expr_to(expr, dest_type);
}

/*******************************************************************\

Function: smv_typecheckt::convert_expr_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert_expr_to(exprt &expr, const typet &type)
{
  PRECONDITION(type.is_not_nil());

  if(expr.type() != type)
  {
    smv_ranget e=convert_type(expr.type());
    smv_ranget t=convert_type(type);

    if(e.is_contained_in(t) && expr.type().id() != ID_enumeration)
    {
      if(e.is_singleton())
      {
        if(type.id()==ID_bool)
        {
          if(e.from==0)
            expr=false_exprt();
          else
            expr=true_exprt();
        }
        else
        {
          expr=exprt(ID_constant, type);
          expr.set(ID_value, integer2string(e.from));
        }
      }
      else
        expr = typecast_exprt{expr, type};

      return;      
    }

    throw errort().with_location(expr.find_source_location())
      << "Expected expression of type `" << to_string(type)
      << "', but got expression `" << to_string(expr) << "', which is of type `"
      << to_string(expr.type()) << "'";
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(exprt &expr, expr_modet expr_mode)
{
  if(expr.id() == ID_smv_next)
  {
    if(expr_mode!=NORMAL)
    {
      throw errort().with_location(expr.find_source_location())
        << "next(next(...)) encountered";
    }
    
    assert(expr.operands().size()==1);

    exprt tmp;
    tmp.swap(to_unary_expr(expr).op());
    expr.swap(tmp);

    convert(expr, NEXT);
    return;
  }

  for(auto &op : expr.operands())
    convert(op, expr_mode);

  if(expr.id()==ID_symbol)
  {
    const std::string &identifier=expr.get_string(ID_identifier);

    if(identifier=="TRUE")
      expr=true_exprt();
    else if(identifier=="FALSE")
      expr=false_exprt();
    else if(identifier.find("::")==std::string::npos)
    {
      std::string id=module+"::var::"+identifier;

      smv_parse_treet::mc_varst::const_iterator it=
        modulep->vars.find(identifier);

      if(it!=modulep->vars.end())
        if(it->second.identifier!="")
          id=id2string(it->second.identifier);

      expr.set(ID_identifier, id);
      
      if(expr_mode==NEXT)
        expr.id(ID_next_symbol);
    }
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
  else if(expr.id()=="smv_cases") // cases
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
  std::string result;
  namespacet ns(symbol_table);
  expr2smv(expr, result, ns);
  return result;
}

/*******************************************************************\

Function: smv_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smv_typecheckt::to_string(const typet &type)
{
  std::string result;
  namespacet ns(symbol_table);
  type2smv(type, result, ns);
  return result;
}

/*******************************************************************\

Function: smv_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::typecheck(
  smv_parse_treet::modulet::itemt &item)
{
  switch(item.item_type)
  {
  case smv_parse_treet::modulet::itemt::INIT:
    typecheck(item.expr, INIT);
    convert_expr_to(item.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::itemt::TRANS:
    typecheck(item.expr, TRANS);
    convert_expr_to(item.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::itemt::CTLSPEC:
    typecheck(item.expr, CTL);
    convert_expr_to(item.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::itemt::LTLSPEC:
    typecheck(item.expr, LTL);
    convert_expr_to(item.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::itemt::INVAR:
  case smv_parse_treet::modulet::itemt::FAIRNESS:
    typecheck(item.expr, OTHER);
    convert_expr_to(item.expr, bool_typet{});
    return;

  case smv_parse_treet::modulet::itemt::ASSIGN_CURRENT:
    typecheck(item.equal_expr().lhs(), OTHER);
    typecheck(item.equal_expr().rhs(), item.equal_expr().lhs().type(), OTHER);
    item.equal_expr().type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::itemt::ASSIGN_INIT:
    typecheck(item.equal_expr().lhs(), INIT);
    typecheck(item.equal_expr().rhs(), item.equal_expr().lhs().type(), INIT);
    item.equal_expr().type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::itemt::ASSIGN_NEXT:
    typecheck(item.equal_expr().lhs(), TRANS);
    typecheck(item.equal_expr().rhs(), item.equal_expr().lhs().type(), TRANS);
    item.equal_expr().type() = bool_typet{};
    return;

  case smv_parse_treet::modulet::itemt::DEFINE:
    typecheck(item.expr, OTHER);
    item.equal_expr().type() = bool_typet{};
    return;
  }
}

/*******************************************************************\

Function: smv_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(
  smv_parse_treet::modulet::itemt &item)
{
  convert(item.expr, NORMAL);
}

/*******************************************************************\

Function: smv_typecheckt::convert_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::convert(smv_parse_treet::mc_varst &vars)
{
  symbolt symbol;

  symbol.mode="SMV";
  symbol.module=modulep->name;

  for(const auto &var_it : vars)
  {
    const smv_parse_treet::mc_vart &var = var_it.second;

    // check the type, if any
    if(var.type.is_not_nil())
      check_type(var.type);

    symbol.base_name = var_it.first;

    if(var.identifier=="")
    {
      symbol.name=module+"::var::"+id2string(symbol.base_name);

      if(module == "smv::main")
        symbol.pretty_name = symbol.base_name;
      else
        symbol.pretty_name = strip_smv_prefix(symbol.name);
    }
    else
      symbol.name=var.identifier;

    symbol.value.make_nil();
    symbol.is_input=true;
    symbol.is_state_var=false;
    symbol.type=var.type;

    symbol_table.add(symbol);
  }
}

/*******************************************************************\

Function: smv_typecheckt::collect_define

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_typecheckt::collect_define(const equal_exprt &expr)
{
  const exprt &lhs = expr.lhs();
  const exprt &rhs = expr.rhs();

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
    throw errort().with_location(expr.find_source_location())
      << "symbol `" << identifier << "' defined twice";
  }  
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
  
  typecheck(d.value, symbol.type, OTHER);
  
  d.in_progress=false;
  d.typechecked=true;

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

  convert(smv_module.vars);

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

    for (auto &item : smv_module.items) {
      convert(item);
    }

    flatten_hierarchy(smv_module);

    // we first need to collect all the defines

    for (auto &item : smv_module.items) {
      if(item.is_define() || item.is_assign_current())
        collect_define(item.equal_expr());
    }
    // now turn them into INVARs
    convert_defines(trans_invar);

    // do the rest now: typecheck
    for (auto &item : smv_module.items) {
      if(!item.is_define() && !item.is_assign_current())
        typecheck(item);
    }

    // copy to transition system
    for(const auto &item : smv_module.items)
    {
      if (item.is_invar())
        trans_invar.push_back(item.expr);
      else if (item.is_init())
        trans_init.push_back(item.expr);
      else if(item.is_assign_init())
        trans_init.push_back(item.expr);
      else if(item.is_assign_next())
        trans_trans.push_back(item.expr);
      else if (item.is_trans())
        trans_trans.push_back(item.expr);
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

    forall_item_list(it, smv_module.items)
    {
      if(it->is_ctlspec() || it->is_ltlspec())
      {
        symbolt spec_symbol;

        if(it->name.has_value())
          spec_symbol.base_name = it->name.value();
        else
          spec_symbol.base_name = "spec" + std::to_string(nr++);

        spec_symbol.name =
          id2string(smv_module.name) + "::" + id2string(spec_symbol.base_name);
        spec_symbol.module = smv_module.name;
        spec_symbol.type = bool_typet();
        spec_symbol.is_property = true;
        spec_symbol.mode = "SMV";
        spec_symbol.value = it->expr;
        spec_symbol.location = it->location;
        spec_symbol.location.set_comment(to_string(it->expr));

        if(smv_module.name == "smv::main")
          spec_symbol.pretty_name = spec_symbol.base_name;
        else
          spec_symbol.pretty_name = strip_smv_prefix(spec_symbol.name);

        symbol_table.add(spec_symbol);
      }
    }
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
  smv_parse_treet::modulest::iterator it=smv_parse_tree.modules.find(module);

  if(it==smv_parse_tree.modules.end())
  {
    throw errort() << "failed to find module " << module;
  }

  convert(it->second);
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
