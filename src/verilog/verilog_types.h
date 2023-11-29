/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPES_H
#define CPROVER_VERILOG_TYPES_H

#include <util/std_types.h>

class verilog_signedbv_typet:public bitvector_typet
{
public:
  inline verilog_signedbv_typet():bitvector_typet(ID_verilog_signedbv)
  {
  }

  explicit inline verilog_signedbv_typet(unsigned width):bitvector_typet(ID_verilog_signedbv, width)
  {
  }
};

/*! \brief Cast a generic typet to a \ref verilog_signedbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilog_signedbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref verilog_signedbv_typet
 *
 * \ingroup gr_std_types
*/
inline const verilog_signedbv_typet &to_verilog_signedbv_type(const typet &type)
{
  assert(type.id()==ID_verilog_signedbv);
  return static_cast<const verilog_signedbv_typet &>(type);
}

/*! \copydoc to_verilog_signedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_signedbv_typet &to_verilog_signedbv_type(typet &type)
{
  assert(type.id()==ID_verilog_signedbv);
  return static_cast<verilog_signedbv_typet &>(type);
}

class verilog_unsignedbv_typet:public bitvector_typet
{
public:
  inline verilog_unsignedbv_typet():bitvector_typet(ID_verilog_unsignedbv)
  {
  }

  explicit inline verilog_unsignedbv_typet(unsigned width):bitvector_typet(ID_verilog_unsignedbv, width)
  {
  }
};

/*! \brief Cast a generic typet to a \ref verilog_unsignedbv_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilog_unsignedbv_typet.
 *
 * \param type Source type
 * \return Object of type \ref verilog_unsignedbv_typet
 *
 * \ingroup gr_std_types
*/
inline const verilog_unsignedbv_typet &to_verilog_unsignedbv_type(const typet &type)
{
  assert(type.id()==ID_verilog_unsignedbv);
  return static_cast<const verilog_unsignedbv_typet &>(type);
}

/*! \copydoc to_verilog_unsignedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_unsignedbv_typet &to_verilog_unsignedbv_type(typet &type)
{
  assert(type.id()==ID_verilog_unsignedbv);
  return static_cast<verilog_unsignedbv_typet &>(type);
}

class module_typet:public typet
{
public:
  inline module_typet():typet(ID_module)
  {
  }
};

class genvar_typet:public typet
{
public:
  inline genvar_typet():typet(ID_genvar)
  {
  }
};

/// 64-bit floating point
class verilog_real_typet:public typet
{
public:
  inline verilog_real_typet():typet(ID_verilog_real)
  {
  }

  std::size_t width() const
  {
    return 64;
  }
};

/// 32-bit floating point
class verilog_shortreal_typet:public typet
{
public:
  inline verilog_shortreal_typet():typet(ID_verilog_shortreal)
  {
  }

  std::size_t width() const
  {
    return 32;
  }
};

/// 64-bit floating point
class verilog_realtime_typet:public typet
{
public:
  inline verilog_realtime_typet():typet(ID_verilog_realtime)
  {
  }

  std::size_t width() const
  {
    return 64;
  }
};

#endif
