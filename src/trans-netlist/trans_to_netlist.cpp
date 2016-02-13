/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/i2string.h>

#include <solvers/prop/aig_prop.h>
#include <solvers/flattening/boolbv_width.h>

#include "netlist.h"
#include "trans_to_netlist.h"
#include "instantiate_netlist.h"

/*******************************************************************\

   Class: convert_trans_to_netlistt

 Purpose:

\*******************************************************************/

class convert_trans_to_netlistt:public messaget
{
public:
  convert_trans_to_netlistt(
    symbol_tablet &_symbol_table,
    netlistt &_dest,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    ns(_symbol_table),
    dest(_dest)
  {
  }

  void operator()(const irep_idt &module);
  
protected:
  symbol_tablet &symbol_table;
  const namespacet ns;
  netlistt &dest;
  
  literalt new_input();

  class rhs_entryt
  {
  public:
    bool converted;
    exprt expr;
    bvt bv;
    unsigned width;
    
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
  bvt transition_constraints;
  
  class rhst
  {
  public:
    rhs_entryt *entry;
    unsigned bit_number;
    
    rhst():entry(0)
    {
    }

    rhst(rhs_entryt &_entry, unsigned _nr):entry(&_entry), bit_number(_nr)
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
    unsigned lhs_from, unsigned lhs_to,
    rhs_entryt &rhs_entry);

  literalt convert_rhs(const rhst &rhs, propt &prop);

  void finalize_lhs(lhs_mapt::iterator, propt &prop);

  void convert_lhs_rec(
    const exprt &expr,
    unsigned from,
    unsigned to,
    propt &prop);

  void convert_constraints(propt &prop);

  void map_vars(
    const irep_idt &module,
    netlistt &dest);
};

/*******************************************************************\

Function: convert_trans_to_netlistt::new_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt convert_trans_to_netlistt::new_input()
{
  irep_idt id="convert::input";

  if(symbol_table.symbols.find(id)==symbol_table.symbols.end())
  {
    symbolt symbol;
    symbol.name=id;
    symbol.type=bool_typet();
    symbol.is_input=true;
    symbol.base_name="input";
    symbol_table.move(symbol);
  }

  var_mapt::vart &var=dest.var_map.map[id];
  var.vartype=var_mapt::vart::VAR_INPUT;
  var.type=bool_typet();
  var.bits.push_back(var_mapt::vart::bitt());
  var_mapt::vart::bitt &bit=var.bits.back();
  bit.current=dest.new_var_node();
  bit.next=const_literal(false); // just to fill it
  return bit.current;
}

/*******************************************************************\

Function: convert_trans_to_netlistt::map_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::map_vars(
  const irep_idt &module,
  netlistt &dest)
{
  boolbv_widtht boolbv_width(ns);

  forall_symbol_module_map(it, symbol_table.symbol_module_map,
                           module)
  {
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(it->second);

    if(s_it==symbol_table.symbols.end())
      continue;

    const symbolt &symbol=s_it->second;

    var_mapt::vart::vartypet vartype;

    if(symbol.is_property)
      continue; // ignore properties
    else if(symbol.type.id()==ID_module ||
            symbol.type.id()==ID_module_instance)
      continue; // ignore modules
    else if(symbol.is_input)
      vartype=var_mapt::vart::VAR_INPUT;
    else if(symbol.is_state_var)
      vartype=var_mapt::vart::VAR_LATCH;
    else
      vartype=var_mapt::vart::VAR_WIRE;

    unsigned size=boolbv_width(symbol.type);
    
    if(size==0)
      continue;

    var_mapt::vart &var=dest.var_map.map[symbol.name];
    var.vartype=vartype;
    var.type=symbol.type;
    var.mode=symbol.mode;
    var.bits.resize(size);
    
    for(unsigned bit=0; bit<size; bit++)
    {
      // just initialize with something
      var.bits[bit].current=const_literal(false);
      var.bits[bit].next=const_literal(false);
        
      // we already know the numbers of inputs and latches
      if(var.is_input() || var.is_latch())
        var.bits[bit].current=dest.new_var_node();
    }
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::operator()(const irep_idt &module)
{
  // setup
  lhs_map.clear();
  rhs_list.clear();
  constraint_list.clear();
  
  map_vars(module, dest);
  
  // setup lhs_map

  for(var_mapt::mapt::iterator
      v_it=dest.var_map.map.begin();
      v_it!=dest.var_map.map.end();
      v_it++)
  {
    bv_varidt bv_varid;
    bv_varid.id=v_it->first;
    var_mapt::vart &var=v_it->second;

    for(bv_varid.bit_nr=0;
        bv_varid.bit_nr<var.bits.size();
        bv_varid.bit_nr++)
    {
      var_mapt::vart::bitt &bit=var.bits[bv_varid.bit_nr];
      lhs_entryt &entry=lhs_map[bv_varid];
      entry.bit=&bit;
      entry.var=&var;
    }
  }

  const symbolt &module_symbol=ns.lookup(module);
  const transt &trans=to_trans_expr(module_symbol.value);

  // build the net-list
  aig_prop_baset aig_prop(dest);
  aig_prop.set_message_handler(get_message_handler());

  // extract constraints from transition relation
  add_constraint(trans.invar());
  add_constraint(trans.trans());

  // do recursive conversion for LHSs
  for(lhs_mapt::iterator
      it=lhs_map.begin();
      it!=lhs_map.end();
      it++)
    finalize_lhs(it, aig_prop);
    
  // finish the var_map
  dest.var_map.build_reverse_map();

  // do the remaining transition constraints
  convert_constraints(aig_prop);
  
  dest.transition.insert(
    dest.transition.end(),
    transition_constraints.begin(),
    transition_constraints.end());
  
  // initial state
  dest.initial.push_back(instantiate_convert(
    aig_prop, dest.var_map, trans.init(), ns, get_message_handler()));

  // find the nondet nodes
  for(unsigned n=0; n<dest.nodes.size(); n++)
  {
    if(dest.nodes[n].is_var())
    {
      const var_mapt::reverse_mapt::const_iterator it=
        dest.var_map.reverse_map.find(n);
      
      if(it==dest.var_map.reverse_map.end())
      {
        bv_varidt varid;
        varid.id="nondet";
        varid.bit_nr=dest.var_map.nondets.size();
        var_mapt::vart &var=dest.var_map.map[varid.id];
        var.add_bit().current=literalt(n, false);
        var.vartype=var_mapt::vart::VAR_NONDET;
        dest.var_map.reverse_map[n]=varid;
        dest.var_map.nondets.insert(n);
      }
    }
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::convert_constraints(propt &prop)
{
  transition_constraints.reserve(
    transition_constraints.size()+constraint_list.size());

  for(constraint_listt::const_iterator
      it=constraint_list.begin();
      it!=constraint_list.end();
      it++)
  {
    literalt l=
      instantiate_convert(prop, dest.var_map, *it, ns, get_message_handler());
    transition_constraints.push_back(l);
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::finalize_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_trans_to_netlistt::finalize_lhs(
  lhs_mapt::iterator lhs_it,
  propt &prop)
{
  lhs_entryt &lhs=lhs_it->second;

  if(lhs.converted) return;
  
  if(lhs.in_progress) // cycle found?
    return;

  if(lhs.equal_to.empty()) // no definition?
  {
    if(lhs.var->is_latch())
    {
      // there needs to be _something_ as next-state value,
      // make it a new input
      lhs.l=lhs.bit->next=new_input();
    }
    else if(lhs.var->is_wire())
    {
      // there needs to be _something_ as value,
      // make it a new input
      lhs.l=lhs.bit->current=new_input();
    }

    return;
  }
    
  // do first one by setting the node appropriately

  lhs.in_progress=true;
  lhs.l=convert_rhs(lhs.equal_to.front(), prop);

  if(lhs.var->is_latch())
    lhs.bit->next=lhs.l;
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
    
    literalt l_rhs=convert_rhs(*it, prop);
    transition_constraints.push_back(
      prop.lequal(lhs.l, l_rhs));
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
  unsigned from, unsigned to,
  propt &prop)
{
  assert(from<=to);

  if(expr.id()==ID_symbol)
  { 
    bv_varidt bv_varid;
    
    bv_varid.id=to_symbol_expr(expr).get_identifier();

    for(bv_varid.bit_nr=from;
        bv_varid.bit_nr<=to;
        bv_varid.bit_nr++)
    {
      lhs_mapt::iterator it=lhs_map.find(bv_varid);

      if(it==lhs_map.end())
        throw "lhs_rec: failed to find `"+bv_varid.as_string()+"' in lhs_map";
      
      // we only need to do wires
      if(!it->second.var->is_wire()) return;
    
      finalize_lhs(it, prop);
    }

    return;
  }
  else if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    mp_integer i;
    if(!to_integer(expr.op1(), i)) // constant?
    {
      from=integer2long(i);
      convert_lhs_rec(expr.op0(), from, from, prop);
      return;
    }
  }
  else if(expr.id()==ID_extractbits)
  {
    mp_integer new_from, new_to;

    assert(expr.operands().size()==3);

    if(!to_integer(expr.op1(), new_from) &&
       !to_integer(expr.op2(), new_to))
    {
      if(new_from>new_to) std::swap(new_from, new_to);
    
      assert(new_from<=new_to);
    
      from=integer2long(new_from);
      to=integer2long(new_to);
    
      convert_lhs_rec(expr.op0(), from, to, prop);
      return;
    }
  }
  
  boolbv_widtht boolbv_width(ns);

  // default
  forall_operands(it, expr)
  {
    unsigned width=boolbv_width(it->type());
    
    if(width==0)
      continue;

    convert_lhs_rec(*it, 0, width-1, prop);
  }
}

/*******************************************************************\

Function: convert_trans_to_netlistt::convert_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt convert_trans_to_netlistt::convert_rhs(
  const rhst &rhs,
  propt &prop)
{
  rhs_entryt &rhs_entry=*rhs.entry;
  
  // done already?
  if(!rhs_entry.converted)
  {
    // get all lhs symbols this depends on
    convert_lhs_rec(rhs_entry.expr, 0, rhs_entry.width-1, prop);

    rhs_entry.converted=true;

    // now we can convert
    instantiate_convert(
      prop, dest.var_map, rhs_entry.expr, ns,
      get_message_handler(), rhs_entry.bv);
      
    assert(rhs_entry.bv.size()==rhs_entry.width);
  }

  assert(rhs.bit_number<rhs_entry.bv.size());
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

  rhs_list.push_back(rhs_entryt(rhs));
  rhs_entryt &rhs_entry=rhs_list.back();
  
  boolbv_widtht boolbv_width(ns);
  rhs_entry.width=boolbv_width(rhs.type());
  
  if(rhs_entry.width==0)
  {
    constraint_list.push_back(src);
    return;
  }
  
  assert(rhs_entry.width!=0);

  unsigned lhs_width=boolbv_width(lhs.type());

  assert(lhs_width==rhs_entry.width);

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
  unsigned lhs_from, unsigned lhs_to,
  rhs_entryt &rhs_entry)
{
  assert(lhs_from<=lhs_to);
  
  if(lhs.id()==ID_next_symbol ||
     lhs.id()==ID_symbol)
  { 
    bool next=lhs.id()==ID_next_symbol;

    bv_varidt bv_varid;
    bv_varid.id=lhs.get(ID_identifier);
    
    for(bv_varid.bit_nr=lhs_from;
        bv_varid.bit_nr!=(lhs_to+1);
        bv_varid.bit_nr++)
    {
      lhs_mapt::iterator it=
        lhs_map.find(bv_varid);

      if(it==lhs_map.end())
        throw "add_equality_rec: failed to find `"+bv_varid.as_string()+"' in lhs_map";

      lhs_entryt &lhs_entry=it->second;
      const var_mapt::vart &var=*lhs_entry.var;
    
      if((next && !var.is_latch()) ||
         (!next && !var.is_wire()))
      {
        // give up
        constraint_list.push_back(src);
        return;
      }

      unsigned rhs_bit_nr=bv_varid.bit_nr-lhs_from;
      lhs_entry.equal_to.push_back(rhst(rhs_entry, rhs_bit_nr));
    }
  }
  else if(lhs.id()==ID_extractbit)
  {
    assert(lhs.operands().size()==2);
    assert(lhs_to==lhs_from);

    mp_integer i;
    if(to_integer(lhs.op1(), i))
      assert(false);

    lhs_from=lhs_from+integer2long(i);
    add_equality_rec(src, lhs.op0(), lhs_from, lhs_from, rhs_entry);
  }
  else if(lhs.id()==ID_extractbits)
  {
    mp_integer op1, op2;

    assert(lhs.operands().size()==3);

    if(to_integer(lhs.op1(), op1))
      throw std::string("failed to convert extractbits op1");
    
    if(to_integer(lhs.op2(), op2))
      throw std::string("failed to convert extractbits op2");
    
    if(op1<op2)
      throw std::string("extractbits op1<op2");

    unsigned new_lhs_to=lhs_from+integer2long(op1);
    unsigned new_lhs_from=lhs_from+integer2long(op2);
    
    add_equality_rec(src, lhs.op0(), new_lhs_from, new_lhs_to, rhs_entry);
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
  symbol_tablet &symbol_table,
  const irep_idt &module,
  netlistt &dest,
  message_handlert &message_handler)
{
  convert_trans_to_netlistt c(symbol_table, dest, message_handler);

  c(module);
}
