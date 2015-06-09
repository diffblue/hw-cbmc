/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPES_H
#define CPROVER_VERILOG_TYPES_H

#include <util/std_types.h>

class verilogbv_typet:public bitvector_typet
{
public:
  inline verilogbv_typet():bitvector_typet(ID_verilogbv)
  {
  }

  explicit inline verilogbv_typet(unsigned width):bitvector_typet(ID_verilogbv, width)
  {
  }
};

/*! \brief Cast a generic typet to a \ref verilogbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilogbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref verilogbv_typet
 *
 * \ingroup gr_std_types
*/
inline const verilogbv_typet &to_verilogbv_type(const typet &type)
{
  assert(type.id()==ID_verilogbv);
  return static_cast<const verilogbv_typet &>(type);
}

/*! \copydoc to_verilogbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilogbv_typet &to_verilogbv_type(typet &type)
{
  assert(type.id()==ID_verilogbv);
  return static_cast<verilogbv_typet &>(type);
}

#endif
