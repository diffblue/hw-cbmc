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
  PRECONDITION(type.id() == ID_verilog_signedbv);
  return static_cast<const verilog_signedbv_typet &>(type);
}

/*! \copydoc to_verilog_signedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_signedbv_typet &to_verilog_signedbv_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_signedbv);
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
  PRECONDITION(type.id() == ID_verilog_unsignedbv);
  return static_cast<const verilog_unsignedbv_typet &>(type);
}

/*! \copydoc to_verilog_unsignedbv_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_unsignedbv_typet &to_verilog_unsignedbv_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_unsignedbv);
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

/// 2-state data type, 16-bit signed integer
class verilog_shortint_typet : public typet
{
public:
  inline verilog_shortint_typet() : typet(ID_verilog_shortint)
  {
  }

  std::size_t width() const
  {
    return 16;
  }
};

/// 2-state data type, 32-bit signed integer
class verilog_int_typet : public typet
{
public:
  inline verilog_int_typet() : typet(ID_verilog_int)
  {
  }

  std::size_t width() const
  {
    return 32;
  }
};

/// 2-state data type, 64-bit signed integer
class verilog_longint_typet : public typet
{
public:
  inline verilog_longint_typet() : typet(ID_verilog_longint)
  {
  }

  std::size_t width() const
  {
    return 64;
  }
};

/// 2-state data type, 8-bit signed integer
class verilog_byte_typet : public typet
{
public:
  inline verilog_byte_typet() : typet(ID_verilog_byte)
  {
  }

  std::size_t width() const
  {
    return 8;
  }
};

/// 2-state data type, for vectors, unsigned
class verilog_bit_typet : public typet
{
public:
  inline verilog_bit_typet() : typet(ID_verilog_bit)
  {
  }
};

/// 4-state data type, for vectors, unsigned
class verilog_logic_typet : public typet
{
public:
  inline verilog_logic_typet() : typet(ID_verilog_logic)
  {
  }
};

/// 4-state data type, for vectors, unsigned
class verilog_reg_typet : public typet
{
public:
  inline verilog_reg_typet() : typet(ID_verilog_reg)
  {
  }
};

/// 4-state data type, 32-bit signed integer
class verilog_integer_typet : public typet
{
public:
  inline verilog_integer_typet() : typet(ID_verilog_integer)
  {
  }

  std::size_t width() const
  {
    return 32;
  }
};

/*! \brief Cast a generic typet to a \ref verilog_integer_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilog_integer_typet.
 *
 * \param type Source type
 * \return Object of type \ref verilog_integer_typet
 *
 * \ingroup gr_std_types
*/
inline const verilog_integer_typet &to_verilog_integer_type(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_integer);
  return static_cast<const verilog_integer_typet &>(type);
}

/*! \copydoc to_verilog_integer_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_integer_typet &to_verilog_integer_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_integer);
  return static_cast<verilog_integer_typet &>(type);
}

/// 4-state data type, 64-bit unsigned integer
class verilog_time_typet : public typet
{
public:
  verilog_time_typet() : typet(ID_verilog_time)
  {
  }

  std::size_t width() const
  {
    return 64;
  }
};

#endif
