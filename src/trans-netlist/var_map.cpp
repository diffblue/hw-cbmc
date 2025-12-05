/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "var_map.h"

#include <ebmc/ebmc_error.h>
#include <solvers/flattening/boolbv_width.h>

/*******************************************************************\

Function: var_mapt::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::add(
  const irep_idt &id,
  unsigned bit_nr,
  const vart &var)
{
  unsigned v_current=var.bits[bit_nr].current.var_no();

  switch(var.vartype)
  {
  case vart::vartypet::LATCH:
    latches.insert(v_current);
    break;
            
  case vart::vartypet::NONDET:
    nondets.insert(v_current);
    break;
            
  case vart::vartypet::INPUT:
    inputs.insert(v_current);
    break;
    
  case vart::vartypet::OUTPUT:
    outputs.insert(v_current);
    break;
    
  case vart::vartypet::WIRE:
    wires.insert(v_current);
    break;

  case vart::vartypet::UNDEF:
  default:;
    break;
  }
  
  if(var.is_latch() || var.is_input())
  {
    bv_varidt &reverse=reverse_map[v_current];
    reverse.id=id;
    reverse.bit_nr=bit_nr;
  }
}

/*******************************************************************\

Function: var_mapt::build_reverse_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::build_reverse_map()
{
  for(mapt::const_iterator
       it=map.begin();
       it!=map.end();
       it++)
  {
    const vart &var=it->second;
    for(std::size_t bit_nr=0; bit_nr<var.bits.size(); bit_nr++)
      add(it->first, bit_nr, var);
  }
}

/*******************************************************************\

Function: var_mapt::get_current

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const var_mapt::vart::bitt &var_mapt::get_bit(
  const irep_idt &id,
  unsigned bit_nr) const
{
  mapt::const_iterator it=map.find(id);

  if(it==map.end())
  {
    throw ebmc_errort() << "failed to find identifier " << id << '[' << bit_nr
                        << "] in var_map";
  }

  if(it->second.bits.size() == 0)
    throw ebmc_errort() << "var_map entry with size zero";

  if(bit_nr>=it->second.bits.size())
  {
    throw ebmc_errort() << "index out of range for " << id << "[" << bit_nr
                        << "]\n"
                           "available range: 0.."
                        << it->second.bits.size() - 1;
  }

  return it->second.bits[bit_nr];
}

/*******************************************************************\

Function: var_mapt::get_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

var_mapt::vart::vartypet var_mapt::get_type(
  const irep_idt &id) const
{
  mapt::const_iterator it=map.find(id);

  if(it==map.end())
  {
    throw ebmc_errort() << "failed to find identifier " << id << " in var_map";
  }

  return it->second.vartype;
}

/*******************************************************************\

Function: var_mapt::reverse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const bv_varidt &var_mapt::reverse(unsigned v) const
{
  reverse_mapt::const_iterator it=reverse_map.find(v);

  if(it==reverse_map.end())
  {
    throw ebmc_errort() << "failed to find variable " << v << " in var_map";
  }

  return it->second;
}

/*******************************************************************\

Function: var_mapt::sorted

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<var_mapt::mapt::const_iterator> var_mapt::sorted() const
{
  using iteratort = mapt::const_iterator;
  std::vector<iteratort> iterators;
  iterators.reserve(map.size());

  for(auto it = map.begin(); it != map.end(); it++)
    iterators.push_back(it);

  std::sort(
    iterators.begin(),
    iterators.end(),
    [](iteratort a, iteratort b) { return a->first.compare(b->first) < 0; });

  return iterators;
}

/*******************************************************************\

Function: var_mapt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void var_mapt::output(std::ostream &out) const
{
  out << "Variable map:" << '\n';

  // sort by identifier to get stable output
  for(auto map_it : sorted())
  {
    const vart &var = map_it->second;

    for(std::size_t i=0; i<var.bits.size(); i++)
    {
      out << "  " << map_it->first;
      if(var.bits.size()!=1) out << "[" << i << "]";
      out << "=";

      literalt l_c=var.bits[i].current;

      if(l_c.is_true())
        out << "true";
      else if(l_c.is_false())
        out << "false";
      else
      {
        if(l_c.sign()) out << "!";
        out << l_c.var_no();
      }
      
      if(var.vartype==vart::vartypet::LATCH)
      {
        out << "->";
        
        literalt l_n=var.bits[i].next;

        if(l_n.is_true())
          out << "true";
        else if(l_n.is_false())
          out << "false";
        else
        {
          if(l_n.sign()) out << "!";
          out << l_n.var_no();
        }
      }
       
      out << " ";

      switch(var.vartype)
      {
       case vart::vartypet::INPUT: out << "(input)"; break;
       case vart::vartypet::LATCH: out << "(latch)"; break;
       case vart::vartypet::NONDET: out << "(nondet)"; break;
       case vart::vartypet::WIRE:  out << "(wire)"; break;
       case vart::vartypet::OUTPUT:out << "(output)"; break;
       case vart::vartypet::UNDEF: out << "(?)"; break;
      }

      out << '\n';
    }
  }

  out << '\n'
      << "Total no. of variable bits: " << reverse_map.size() << '\n'
      << "Total no. of latch bits: " << latches.size() << '\n'
      << "Total no. of nondet bits: " << nondets.size() << '\n'
      << "Total no. of input bits: " << inputs.size() << '\n'
      << "Total no. of output bits: " << outputs.size() << '\n';
}
