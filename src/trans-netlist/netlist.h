/*******************************************************************\

Module: Graph representing Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_H
#define CPROVER_TRANS_NETLIST_H

#include <util/expr.h>

#include "aig.h"
#include "var_map.h"

#include <iosfwd>
#include <variant>

class netlistt:public aig_plus_constraintst
{
public:
  var_mapt var_map;
  
  netlistt()
  {
  }
  
  virtual ~netlistt()
  {
  }

  unsigned get_no_vars() const
  {
    return var_map.get_no_vars();
  }
  
  using aigt::print;
  virtual void print(std::ostream &out) const;
  virtual void output_dot(std::ostream &out) const;
  virtual void output_smv(std::ostream &out) const;
  virtual std::string label(unsigned n) const;
  virtual std::string dot_label(unsigned n) const;
  
  void swap(netlistt &other)
  {
    aigt::swap(other);
    other.var_map.swap(var_map);
    initial.swap(other.initial);
    transition.swap(other.transition);
  }
  
  // additional constraints, given as netlist literals
  // these are implicit conjunctions
  bvt initial;
  bvt transition;

  // Map from property ID to a netlist property,
  // which uses literal_exprt.
  using propertiest = std::map<irep_idt, exprt>;
  propertiest properties;

protected:
  static std::string id2smv(const irep_idt &id);
  void print_smv(std::ostream &, literalt) const;
  void print_smv(std::ostream &, const exprt &) const;
};

#endif
