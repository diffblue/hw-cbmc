/*******************************************************************\

Module: Variable Mapping

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_VAR_MAP_H
#define CPROVER_TRANS_VAR_MAP_H

#include "bv_varid.h"

#include <solvers/prop/prop.h>

#include <util/type.h>

#include <map>
#include <set>
#include <vector>
#include <string>

class var_mapt
{
public:
  struct vart
  {
    enum class vartypet { UNDEF, LATCH, INPUT,
                          OUTPUT, WIRE, NONDET };
    vartypet vartype;
    typet type;
    irep_idt mode;
    
    inline bool is_latch() const { return vartype==vartypet::LATCH; }
    inline bool is_input() const { return vartype==vartypet::INPUT; }
    inline bool is_output() const
    {
      return vartype == vartypet::OUTPUT;
    }
    inline bool is_wire() const { return vartype==vartypet::WIRE; }
    inline bool is_nondet() const { return vartype==vartypet::NONDET; }
    bool has_next() const
    {
      return is_latch() || is_input() || is_wire() || is_output();
    }

    struct bitt
    {
      // these are not guaranteed to be positive
      literalt current, next;
    };
     
    typedef std::vector<bitt> bitst;
    bitst bits;
    
    inline bitt &add_bit()
    {
      bits.push_back(bitt());
      return bits.back();
    }
    
    inline vart():vartype(vartypet::UNDEF)
    {
    }
  };

  /// record variable given by its number as nondet
  void record_as_nondet(literalt::var_not);

  void add(const irep_idt &id, unsigned bit_nr, const vart &var);
  
  void build_reverse_map();
  
  vart::vartypet get_type(const irep_idt &id) const;

  typedef std::unordered_map<irep_idt, vart, irep_id_hash> mapt;
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
    other.nondets.swap(nondets);
    other.wires.swap(wires);
    other.map.swap(map);
  }
  
  void clear()
  {
    reverse_map.clear();
    latches.clear();
    inputs.clear();
    nondets.clear();
    outputs.clear();
    wires.clear();
    map.clear();
  }

  std::vector<mapt::const_iterator> sorted() const;
  std::vector<mapt::iterator> sorted();
};
 
#endif
