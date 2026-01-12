/*******************************************************************\

Module: Variable Mapping

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_BV_VARID_H
#define CPROVER_TRANS_BV_VARID_H

#include <iosfwd>

#include <util/irep.h>

class bv_varidt
{
public:
  irep_idt id;
  std::size_t bit_nr;
  bool next;

  friend bool operator==(const bv_varidt &i1, const bv_varidt &i2)
  {
    return i1.id == i2.id && i1.bit_nr == i2.bit_nr && i1.next == i2.next;
  }
   
  friend bool operator<(const bv_varidt &i1, const bv_varidt &i2)
  {
    if(i1.id==i2.id)
    {
      if(i1.bit_nr == i2.bit_nr)
        return i1.next < i2.next;
      else
        return i1.bit_nr < i2.bit_nr;
    }
    else
      return i1.id < i2.id;
  }

  inline bv_varidt(const irep_idt &_id, std::size_t _bit_nr, bool _next)
    : id(_id), bit_nr(_bit_nr), next(_next)
  { }

  std::string as_string() const;
};

static inline std::ostream & operator<< (std::ostream &out, const bv_varidt &v)
{
  return out << v.as_string();
}
 
struct bv_varidt_hash
{
  size_t operator()(const bv_varidt &bv_varid) const
  {
    return hash_string(bv_varid.id) ^ bv_varid.bit_nr ^ bv_varid.next;
  }
};
 
#endif
