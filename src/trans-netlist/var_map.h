/*******************************************************************\

Module: Variable Mapping

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_VAR_MAP_H
#define CPROVER_TRANS_VAR_MAP_H

#include <map>
#include <set>
#include <vector>
#include <string>

#include <util/symbol_table.h>

#include <solvers/prop/prop.h>

#include "bv_varid.h"

class var_mapt
{
public:
  struct vart
  {
    typedef enum { VAR_UNDEF, VAR_LATCH, VAR_INPUT,
                   VAR_OUTPUT, VAR_WIRE, VAR_NONDET } vartypet;
    vartypet vartype;
    typet type;
    irep_idt mode;
    
    bool is_latch() const { return vartype==VAR_LATCH; }
    bool is_input() const { return vartype==VAR_INPUT; }
    bool is_wire() const { return vartype==VAR_WIRE; }
    bool is_nondet() const { return vartype==VAR_NONDET; }
    
    struct bitt
    {
      // these are not guaranteed to be positive
      literalt current, next;
    };
     
    typedef std::vector<bitt> bitst;
    bitst bits;
    
    vart():vartype(VAR_UNDEF)
    {
    }
  };
  
  void add(const irep_idt &id, unsigned bit_nr, const vart &var);
  
  void build_reverse_map();
  
  vart::vartypet get_type(const irep_idt &id) const;

  typedef hash_map_cont<irep_idt, vart, irep_id_hash> mapt;
  mapt map;
  
  typedef std::map<unsigned, bv_varidt> reverse_mapt;
  reverse_mapt reverse_map;

  const bv_varidt &reverse(unsigned v) const;

  void output(std::ostream &out) const;
  
  unsigned get_no_vars() const
  {
    return reverse_map.size();
  }
  
  const vart::bitt &get_bit(const irep_idt &id, unsigned bit_nr) const;
  
  inline literalt get_current(const irep_idt &id, unsigned bit_nr) const
  {
    return get_bit(id, bit_nr).current;
  }

  inline literalt get_current(const bv_varidt &varid) const
  {
    return get_current(varid.id, varid.bit_nr);
  }
  
  inline literalt get_next(const irep_idt &id, unsigned bit_nr) const
  {
    return get_bit(id, bit_nr).next;
  }

  inline literalt get_next(const bv_varidt &varid) const
  {
    return get_next(varid.id, varid.bit_nr);
  }
  
  typedef std::set<unsigned> var_sett;

  var_sett latches, inputs, outputs, wires, nondets;
  
  var_mapt()
  {
  }
  
  void swap(var_mapt &other)
  {
    std::swap(other.reverse_map, reverse_map);
    other.latches.swap(latches);
    other.inputs.swap(inputs);
    other.outputs.swap(outputs);
    other.wires.swap(wires);
    other.map.swap(map);
  }
  
  void clear()
  {
    reverse_map.clear();
    latches.clear();
    inputs.clear();
    outputs.clear();
    wires.clear();
    map.clear();
  }
};
 
#endif
