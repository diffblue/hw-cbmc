/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "trans_to_netlist.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/prop/literal_expr.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/sva_to_ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "aig_prop.h"
#include "build_netlist_var_map.h"
#include "netlist.h"
#include "netlist_boolbv.h"

#include <algorithm>

/*******************************************************************\

   Class: convert_trans_to_netlistt

 Purpose:

\*******************************************************************/

class convert_trans_to_netlistt:public messaget
{
public:
  convert_trans_to_netlistt(
    symbol_table_baset &_symbol_table,
    netlistt &_dest,
    message_handlert &_message_handler)
    : messaget(_message_handler),
      symbol_table(_symbol_table),
      ns(_symbol_table),
      dest(_dest),
      aig_prop(dest, _message_handler),
      solver(ns, aig_prop, _message_handler, dest.var_map)
  {
  }

  void operator()(
    const irep_idt &module,
    const transt &,
    const std::map<irep_idt, exprt> &properties);

protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  netlistt &dest;
  aig_prop_constraintt aig_prop;
  netlist_boolbvt solver;

  literalt new_input();
  std::size_t input_counter = 0;
  irep_idt mode;

  class rhs_entryt
  {
  public:
    bool converted;
    exprt expr;
    bvt bv;
    std::size_t width = 0;

    rhs_entryt():converted(false)
    {
    }

    rhs_entryt(const exprt &_expr):converted(false), expr(_expr)
    {
    }
  };

  typedef std::list<rhs_entryt> rhs_listt;
  rhs_listt rhs_list;

  typedef std::list<exprt> constraint_listt;
  constraint_listt constraint_list;

  bvt invar_constraints, transition_constraints;

  class rhst
  {
  public:
    rhs_entryt *entry;
    std::size_t bit_number;

    rhst():entry(0)
    {
    }

    rhst(rhs_entryt &_entry, std::size_t _nr):entry(&_entry), bit_number(_nr)
    {
    }
  };

  class lhs_entryt
  {
  public:
    std::list<rhst> equal_to;
    bool converted, in_progress;
    literalt l;

    // link to varmap
    var_mapt::vart *var;
    var_mapt::vart::bitt *bit;

    lhs_entryt():converted(false), in_progress(false), l(const_literal(false))
    {
    }
  };

  typedef std::map<bv_varidt, lhs_entryt> lhs_mapt;
  lhs_mapt lhs_map;

  void add_constraint(const exprt &src);
  void add_equality(const equal_exprt &src);

  void add_equality_rec(
    const equal_exprt &src,
    const exprt &lhs,
    std::size_t lhs_from, std::size_t lhs_to,
    rhs_entryt &rhs_entry);

  literalt convert_rhs(const rhst &);

  void finalize_lhs(lhs_mapt::iterator);

  void convert_lhs_rec(const exprt &expr, std::size_t from, std::size_t to);

  void convert_constraints();

  std::optional<exprt> convert_property(const exprt &);

  void allocate_state_variables(netlistt &);
};

/*******************************************************************\

Function: convert_trans_to_netlistt::new_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt convert_trans_to_netlistt::new_input()
{
  irep_idt id = "convert::input" + std::to_string(input_counter++);

  if(symbol_table.symbols.find(id)==symbol_table.symbols.end())
  {
    symbolt symbol{id, bool_typet(), mode};
    symbol.is_input=true;
    symbol.base_name="input";
    symbol_table.add(symbol);
  }

  var_mapt::vart &var=dest.var_map.map[id];
  var.vartype=var_mapt::vart::vartypet::INPUT;
  var.type=bool_typet();
  var.bits.push_back(var_mapt::vart::bitt());
  var_mapt::vart::bitt &bit=var.bits.back();
  bit.current=dest.new_var_node();
  bit.next=const_literal(false); // just to fill it
  return bit.current;
}

/*******************************************************************\

Function: convert_trans_to_netlistt::allocate_state_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::allocate_state_variables(netlistt &dest)
{
  // we work with the sorted var_map to get a deterministic
  // allocation for the latches and inputs

  for(auto var_map_it : dest.var_map.sorted())
  {
    auto &var = var_map_it->second;

    for(auto &bit : var.bits)
    {
      // just initialize with something
      bit.current = const_literal(false);
      bit.next = const_literal(false);

      if(var.is_input() || var.is_latch())
        bit.current = dest.new_var_node();
    }
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::operator()(
  const irep_idt &module,
  const transt &trans,
  const std::map<irep_idt, exprt> &properties)
{
  // setup
  lhs_map.clear();
  rhs_list.clear();
  constraint_list.clear();

  dest.var_map = build_netlist_var_map(symbol_table, module);
  allocate_state_variables(dest);

  // setup lhs_map

  for(var_mapt::mapt::iterator
      v_it=dest.var_map.map.begin();
      v_it!=dest.var_map.map.end();
      v_it++)
  {
    var_mapt::vart &var=v_it->second;

    for(std::size_t bit_nr = 0; bit_nr < var.bits.size(); bit_nr++)
    {
      bv_varidt bv_varid{v_it->first, bit_nr};
      var_mapt::vart::bitt &bit=var.bits[bv_varid.bit_nr];
      lhs_entryt &entry=lhs_map[bv_varid];
      entry.bit=&bit;
      entry.var=&var;
    }
  }

  mode = ns.lookup(module).mode;

  // extract constraints from transition relation
  add_constraint(trans.invar());
  add_constraint(trans.trans());

  // do recursive conversion for LHSs
  for(lhs_mapt::iterator
      it=lhs_map.begin();
      it!=lhs_map.end();
      it++)
  {
    finalize_lhs(it);
  }

  // finish the var_map
  dest.var_map.build_reverse_map();

  // do the remaining transition constraints
  convert_constraints();

  dest.constraints.insert(
    dest.constraints.end(), invar_constraints.begin(), invar_constraints.end());

  dest.transition.insert(
    dest.transition.end(),
    transition_constraints.begin(),
    transition_constraints.end());

  // initial state
  dest.initial.push_back(solver.convert(trans.init()));

  // properties
  for(const auto &[id, property_expr] : properties)
  {
    auto netlist_expr_opt = convert_property(property_expr);
    dest.properties.emplace(id, netlist_expr_opt);
  }

  // find the nondet nodes
  for(std::size_t n=0; n<dest.nodes.size(); n++)
  {
    if(dest.nodes[n].is_var())
    {
      const var_mapt::reverse_mapt::const_iterator it=
        dest.var_map.reverse_map.find(n);

      if(it==dest.var_map.reverse_map.end())
        dest.var_map.record_as_nondet(n);
    }
  }

  // label the AIG nodes
  for(auto var_map_it : dest.var_map.sorted())
  {
    auto &var = var_map_it->second;

    for(std::size_t bit_nr = 0; bit_nr < var.bits.size(); bit_nr++)
    {
      std::string label = id2string(var_map_it->first);
      if(var.bits.size() != 1)
        label += '[' + std::to_string(bit_nr) + ']';

      dest.label(var.bits[bit_nr].current, label);

      if(var.is_latch())
        dest.label(var.bits[bit_nr].next, label + '\'');
    }
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<exprt>
convert_trans_to_netlistt::convert_property(const exprt &expr)
{
  if(is_temporal_operator(expr))
  {
    if(is_LTL_operator(expr) || is_CTL_operator(expr))
    {
      exprt copy = expr;
      for(auto &op : copy.operands())
      {
        auto op_opt = convert_property(op);
        if(op_opt.has_value())
          op = op_opt.value();
        else
          return {};
      }
      return copy;
    }
    else if(is_SVA_operator(expr))
    {
      // Try to turn into LTL
      try
      {
        auto LTL = SVA_to_LTL(expr);
        return convert_property(LTL);
      }
      catch(sva_to_ltl_unsupportedt)
      {
        return {};
      }
    }
    else
      return {};
  }
  else if(!has_temporal_operator(expr))
  {
    auto l = solver.convert(expr);
    return literal_exprt{l};
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_not ||
    expr.id() == ID_implies || expr.id() == ID_xor || expr.id() == ID_xnor ||
    (expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool))
  {
    exprt copy = expr;
    for(auto &op : copy.operands())
    {
      auto op_opt = convert_property(op);
      if(op_opt.has_value())
        op = op_opt.value();
      else
        return {};
    }
    return copy;
  }
  else
  {
    // contains temporal operator, but not propositional skeleton
    return {};
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::convert_constraints()
{
  invar_constraints.reserve(
    transition_constraints.size() + constraint_list.size());

  transition_constraints.reserve(
    transition_constraints.size()+constraint_list.size());

  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
  {
    literalt l = solver.convert(*it);

    if(has_subexpr(*it, ID_next_symbol))
      transition_constraints.push_back(l);
    else
      invar_constraints.push_back(l);
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::finalize_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::finalize_lhs(lhs_mapt::iterator lhs_it)
{
  lhs_entryt &lhs=lhs_it->second;

  if(lhs.converted) return;

  if(lhs.in_progress) // cycle found?
  {
    // The bit is read while it is being converted. The read yields an
    // unconstrained value rather than the placeholder.
    if(lhs.var->is_latch())
    {
      // The next-state value of a latch, which is constrained to
      // equal its definition below.
      if(lhs.bit->next.is_constant())
        lhs.bit->next = dest.new_var_node();
    }
    else if(lhs.bit->current.is_constant())
      lhs.bit->current = dest.new_var_node();
    return;
  }

  if(lhs.equal_to.empty()) // no definition?
  {
    // Every read of the bit needs to yield the same value.
    lhs.converted = true;

    if(lhs.var->is_latch())
    {
      // there needs to be _something_ as next-state value,
      // make it a new input
      lhs.l=lhs.bit->next=new_input();
    }
    else if(lhs.var->is_wire() || lhs.var->is_output())
    {
      // there needs to be _something_ as value,
      // make it a new input
      lhs.l=lhs.bit->current=new_input();
    }

    return;
  }

  // do first one by setting the node appropriately

  lhs.in_progress=true;

  lhs.l = convert_rhs(lhs.equal_to.front());

  if(lhs.var->is_latch())
  {
    // Was the next-state value read while it was converted? Then the
    // value that was read must equal the definition.
    if(!lhs.bit->next.is_constant())
      transition_constraints.push_back(aig_prop.lequal(lhs.bit->next, lhs.l));

    lhs.bit->next = lhs.l;
  }
  else
    lhs.bit->current=lhs.l;

  lhs.converted=true;
  lhs.in_progress=false;

  // do any additional constraints

  for(std::list<rhst>::const_iterator
      it=lhs.equal_to.begin();
      it!=lhs.equal_to.end();
      it++)
  {
    // first one? -- already done
    if(it==lhs.equal_to.begin()) continue;

    literalt l_rhs = convert_rhs(*it);
    transition_constraints.push_back(aig_prop.lequal(lhs.l, l_rhs));
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_lhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::convert_lhs_rec(
  const exprt &expr,
  std::size_t from,
  std::size_t to)
{
  PRECONDITION(from <= to);

  if(expr.id()==ID_symbol)
  {
    auto identifier = to_symbol_expr(expr).identifier();

    for(std::size_t bit_nr = from; bit_nr <= to; bit_nr++)
    {
      bv_varidt bv_varid{identifier, bit_nr};
      lhs_mapt::iterator it=lhs_map.find(bv_varid);

      if(it==lhs_map.end())
        throw ebmc_errort{} << "lhs_rec: failed to find `"
                            << bv_varid.as_string() << "' in lhs_map";

      // we only need to do wires and outputs
      if(!it->second.var->is_wire() && !it->second.var->is_output())
        return;

      finalize_lhs(it);
    }

    return;
  }
  else if(expr.id() == ID_next_symbol)
  {
    // The next-state value of a latch is given by its definition,
    // which needs to be converted first.
    auto identifier = expr.get(ID_identifier);

    for(std::size_t bit_nr = from; bit_nr <= to; bit_nr++)
    {
      bv_varidt bv_varid{identifier, bit_nr};
      lhs_mapt::iterator it = lhs_map.find(bv_varid);

      if(it == lhs_map.end())
        throw ebmc_errort{} << "lhs_rec: failed to find `"
                            << bv_varid.as_string() << "' in lhs_map";

      if(!it->second.var->is_latch())
        return;

      finalize_lhs(it);
    }

    return;
  }
  else if(expr.id()==ID_extractbit)
  {
    mp_integer i;
    if(!to_integer_non_constant(
         to_extractbit_expr(expr).index(), i)) // constant?
    {
      from = i.to_ulong();
      convert_lhs_rec(to_extractbit_expr(expr).src(), from, from);
      return;
    }
  }
  else if(expr.id()==ID_extractbits)
  {
    mp_integer new_from;

    if(!to_integer_non_constant(to_extractbits_expr(expr).index(), new_from))
    {
      boolbv_widtht boolbv_width(ns);
      const auto width = boolbv_width(expr.type());
      DATA_INVARIANT(
        width != 0, "trans_to_netlist got extractbits with zero-width operand");
      mp_integer new_to = new_from + width - 1;

      from = new_from.to_ulong();
      to = new_to.to_ulong();

      convert_lhs_rec(to_extractbits_expr(expr).src(), from, to);
      return;
    }
  }
  else if(
    (expr.id() == ID_concatenation || expr.id() == ID_array) &&
    std::all_of(
      expr.operands().begin(),
      expr.operands().end(),
      [](const exprt &op)
      {
        return can_cast_type<bitvector_typet>(op.type()) ||
               op.type().id() == ID_bool;
      }))
  {
    // Distribute [from, to] over the operands. The operands of a
    // concatenation are most significant first; the elements of an
    // array constructor are element 0 first.
    const bool is_concat = expr.id() == ID_concatenation;
    boolbv_widtht boolbv_width(ns);
    std::size_t offset = is_concat ? boolbv_width(expr.type()) : 0;

    for(auto &op : expr.operands())
    {
      const std::size_t op_width = boolbv_width(op.type());
      if(op_width == 0)
        continue;

      if(is_concat)
        offset -= op_width;

      const std::size_t lo = std::max(from, offset);
      const std::size_t hi = std::min(to, offset + op_width - 1);

      if(lo <= hi)
        convert_lhs_rec(op, lo - offset, hi - offset);

      if(!is_concat)
        offset += op_width;
    }

    return;
  }
  else if(expr.id() == ID_index)
  {
    // An element of an array with a constant index reads the bits
    // [i*w, (i+1)*w) of the array, where w is the element width.
    auto &index_expr = to_index_expr(expr);
    mp_integer i;

    // Only for one-dimensional arrays of bitvector or Boolean elements;
    // the bit layout of nested arrays and arrays of structs is left to
    // the default case.
    const bool simple_element = can_cast_type<bitvector_typet>(expr.type()) ||
                                expr.type().id() == ID_bool;

    if(
      simple_element && index_expr.array().type().id() == ID_array &&
      !to_integer_non_constant(index_expr.index(), i) && i >= 0)
    {
      boolbv_widtht boolbv_width(ns);
      const std::size_t element_width = boolbv_width(expr.type());
      const std::size_t array_width = boolbv_width(index_expr.array().type());
      const auto offset = numeric_cast_v<std::size_t>(i) * element_width;

      if(element_width != 0 && to + offset < array_width)
      {
        convert_lhs_rec(index_expr.array(), from + offset, to + offset);
        return;
      }
    }
  }
  else if(expr.id() == ID_lshr)
  {
    // Bits [from, to] of a logical right shift by a constant are the bits
    // [from + distance, to + distance] of the shifted operand, as far as
    // these exist; the remaining bits are zero.
    auto &shift = to_shift_expr(expr);
    mp_integer distance;

    if(!to_integer_non_constant(shift.distance(), distance) && distance >= 0)
    {
      boolbv_widtht boolbv_width(ns);
      const std::size_t op_width = boolbv_width(shift.op().type());
      const auto d = numeric_cast_v<std::size_t>(distance);

      if(op_width != 0 && from + d < op_width)
      {
        convert_lhs_rec(shift.op(), from + d, std::min(to + d, op_width - 1));
      }

      return;
    }
  }

  boolbv_widtht boolbv_width(ns);

  // default
  forall_operands(it, expr)
  {
    // natural/integer-typed expressions do not contain symbols, and hence,
    // do not need to be recursed into.
    if(it->type().id() == ID_natural || it->type().id() == ID_integer)
      continue;

    std::size_t width=boolbv_width(it->type());

    if(width==0)
      continue;

    convert_lhs_rec(*it, 0, width - 1);
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt convert_trans_to_netlistt::convert_rhs(const rhst &rhs)
{
  rhs_entryt &rhs_entry=*rhs.entry;

  // done already?
  if(!rhs_entry.converted)
  {
    // get all lhs symbols this depends on
    convert_lhs_rec(rhs_entry.expr, 0, rhs_entry.width - 1);

    rhs_entry.converted=true;

    // now we can convert
    rhs_entry.bv = solver.convert_bv(rhs_entry.expr);

    DATA_INVARIANT(rhs_entry.bv.size() == rhs_entry.width, "bit-width match");
  }

  DATA_INVARIANT(rhs.bit_number < rhs_entry.bv.size(), "bit index in range");
  return rhs_entry.bv[rhs.bit_number];
}

/*******************************************************************\

Function: convert_trans_to_netlistt::add_equality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::add_equality(const equal_exprt &src)
{
  const exprt &lhs=src.lhs();
  const exprt &rhs=src.rhs();

  // A concatenation on the right-hand side is split into one equality per
  // operand, on the corresponding bits of the left-hand side. The bits of
  // the left-hand side are converted on demand, by converting the entire
  // right-hand side that defines them. Without the split, a wire whose
  // slices are defined in terms of other slices of the same wire, e.g.,
  // v == { v[1:0] + 1, 2'b01 }, would appear to depend on itself.
  {
    const exprt *concat = &rhs;

    // look through a typecast between bit-vector types of the same width
    if(
      concat->id() == ID_typecast &&
      can_cast_type<bitvector_typet>(concat->type()) &&
      can_cast_type<bitvector_typet>(to_typecast_expr(*concat).op().type()) &&
      to_bitvector_type(concat->type()).get_width() ==
        to_bitvector_type(to_typecast_expr(*concat).op().type()).get_width())
    {
      concat = &to_typecast_expr(*concat).op();
    }

    boolbv_widtht boolbv_width(ns);

    // The operands of a concatenation are most significant first;
    // the elements of an array constructor are element 0 first.
    const bool is_concat = concat->id() == ID_concatenation;
    const bool is_array = concat->id() == ID_array;

    // Only split when every operand is a bitvector or Boolean; the bit
    // layout of struct and nested-array elements is left to the
    // unsplit conversion.
    const bool simple_operands =
      (is_concat || is_array) &&
      std::all_of(
        concat->operands().begin(),
        concat->operands().end(),
        [](const exprt &op)
        {
          return can_cast_type<bitvector_typet>(op.type()) ||
                 op.type().id() == ID_bool;
        });

    if(
      simple_operands && concat->operands().size() >= 2 &&
      boolbv_width(lhs.type()) == boolbv_width(concat->type()) &&
      boolbv_width(lhs.type()) != 0)
    {
      std::size_t offset = is_concat ? boolbv_width(concat->type()) : 0;

      for(auto &op : concat->operands())
      {
        auto op_width = boolbv_width(op.type());
        if(op_width == 0)
          continue;

        if(is_concat)
          offset -= op_width;

        exprt lhs_part;

        // Simplify, to resolve selects of the wire with constant indices,
        // e.g., (v >> (2 - 1) * 2)[1:0], into extracts of the bits they
        // read, which the dependency analysis of the wire's bits needs.
        exprt rhs_part = simplify_expr(op, ns);

        if(op.type().id() == ID_bool)
        {
          lhs_part =
            extractbit_exprt{lhs, from_integer(offset, integer_typet{})};
        }
        else
        {
          auto part_type = unsignedbv_typet{op_width};
          lhs_part = extractbits_exprt{
            lhs, from_integer(offset, integer_typet{}), part_type};
          rhs_part = typecast_exprt::conditional_cast(rhs_part, part_type);
        }

        add_equality(equal_exprt{std::move(lhs_part), std::move(rhs_part)});

        if(is_array)
          offset += op_width;
      }

      return;
    }
  }

  rhs_list.push_back(rhs_entryt(rhs));
  rhs_entryt &rhs_entry=rhs_list.back();

  boolbv_widtht boolbv_width(ns);
  rhs_entry.width=boolbv_width(rhs.type());

  if(rhs_entry.width==0)
  {
    constraint_list.push_back(src);
    return;
  }

  DATA_INVARIANT(rhs_entry.width != 0, "no empty entries");

  std::size_t lhs_width=boolbv_width(lhs.type());

  DATA_INVARIANT(lhs_width == rhs_entry.width, "bit-width match");

  add_equality_rec(src, lhs, 0, lhs_width-1, rhs_entry);
}

/*******************************************************************\

Function: convert_trans_to_netlistt::add_equality_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::add_equality_rec(
  const equal_exprt &src,
  const exprt &lhs,
  std::size_t lhs_from, std::size_t lhs_to,
  rhs_entryt &rhs_entry)
{
  PRECONDITION(lhs_from <= lhs_to);

  if(lhs.id()==ID_next_symbol ||
     lhs.id()==ID_symbol)
  {
    bool next=lhs.id()==ID_next_symbol;
    auto identifier = lhs.get(ID_identifier);

    for(std::size_t bit_nr = lhs_from; bit_nr != (lhs_to + 1); bit_nr++)
    {
      bv_varidt bv_varid{identifier, bit_nr};
      lhs_mapt::iterator it=
        lhs_map.find(bv_varid);

      if(it==lhs_map.end())
        throw ebmc_errort{} << "add_equality_rec: failed to find `"
                            << bv_varid.as_string() << "' in lhs_map";

      lhs_entryt &lhs_entry=it->second;
      const var_mapt::vart &var=*lhs_entry.var;

      if(
        (next && !var.is_latch()) ||
        (!next && !var.is_wire() && !var.is_output()))
      {
        // give up
        constraint_list.push_back(src);
        return;
      }

      std::size_t rhs_bit_nr=bv_varid.bit_nr-lhs_from;
      lhs_entry.equal_to.push_back(rhst(rhs_entry, rhs_bit_nr));
    }
  }
  else if(lhs.id()==ID_extractbit)
  {
    PRECONDITION(lhs_to == lhs_from);

    mp_integer i;
    if(to_integer_non_constant(to_extractbit_expr(lhs).index(), i))
      PRECONDITION(false);

    lhs_from = lhs_from + i.to_ulong();
    add_equality_rec(
      src, to_extractbit_expr(lhs).src(), lhs_from, lhs_from, rhs_entry);
  }
  else if(lhs.id()==ID_extractbits)
  {
    mp_integer index;

    if(to_integer_non_constant(to_extractbits_expr(lhs).index(), index))
      throw std::string("failed to convert extractbits index");

    boolbv_widtht boolbv_width(ns);

    const auto width = boolbv_width(lhs.type());

    DATA_INVARIANT(width != 0, "add_equality_rec got zero-width bit-vector");

    DATA_INVARIANT(
      lhs_to - lhs_from < width, "add_equality_rec range within extract");

    std::size_t new_lhs_from = lhs_from + index.to_ulong();
    std::size_t new_lhs_to = lhs_to + index.to_ulong();

    add_equality_rec(
      src, to_extractbits_expr(lhs).src(), new_lhs_from, new_lhs_to, rhs_entry);
  }
  else
    constraint_list.push_back(src);
}

/*******************************************************************\

Function: convert_trans_to_netlistt::add_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::add_constraint(const exprt &src)
{
  if(src.id()==ID_equal)
  {
    add_equality(to_equal_expr(src));
  }
  else if(src.id()==ID_and)
  {
    forall_operands(it, src)
      add_constraint(*it);
  }
  else
    constraint_list.push_back(src);
}

/*******************************************************************\

Function: convert_trans_to_netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlist(
  symbol_table_baset &symbol_table,
  const irep_idt &module,
  const transt &trans_expr,
  const std::map<irep_idt, exprt> &properties,
  netlistt &dest,
  message_handlert &message_handler)
{
  convert_trans_to_netlistt c(symbol_table, dest, message_handler);

  c(module, trans_expr, properties);
}
