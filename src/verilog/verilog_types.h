/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPES_H
#define CPROVER_VERILOG_TYPES_H

#include <util/std_types.h>

/// Used during elaboration only,
/// to signal that a symbol is yet to be elaborated.
class to_be_elaborated_typet : public type_with_subtypet
{
public:
  explicit to_be_elaborated_typet(typet type)
    : type_with_subtypet(ID_to_be_elaborated, std::move(type))
  {
  }
};

/// Used during elaboration only,
/// to signal that the type of the symbol is going to be the
/// type of the value (default for parameters).
class derive_from_value_typet : public typet
{
public:
  derive_from_value_typet() : typet(ID_derive_from_value)
  {
  }
};

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

class verilog_genvar_typet : public typet
{
public:
  verilog_genvar_typet() : typet(ID_verilog_genvar)
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

class verilog_enum_typet : public type_with_subtypet
{
public:
  class enum_namet : public irept
  {
  public:
    const exprt &value() const
    {
      return static_cast<const exprt &>(find(ID_value));
    }

    exprt &value()
    {
      return static_cast<exprt &>(add(ID_value));
    }

    irep_idt identifier() const
    {
      return get(ID_identifier);
    }

    void identifier(irep_idt _identifier)
    {
      set(ID_identifier, _identifier);
    }

    irep_idt base_name() const
    {
      return get(ID_base_name);
    }

    void base_name(irep_idt _base_name)
    {
      set(ID_base_name, _base_name);
    }
  };

  using enum_namest = std::vector<enum_namet>;

  verilog_enum_typet(typet _base_type, enum_namest _enum_names)
    : type_with_subtypet(ID_verilog_enum, std::move(_base_type))
  {
    enum_names() = std::move(_enum_names);
  }

  const typet &base_type() const
  {
    return subtype();
  }

  typet &base_type()
  {
    return subtype();
  }

  bool has_base_type() const
  {
    return base_type().is_not_nil();
  }

  const enum_namest &enum_names() const
  {
    return (const enum_namest &)(find(ID_enum_names).get_sub());
  }

  enum_namest &enum_names()
  {
    return (enum_namest &)(add(ID_enum_names).get_sub());
  }

  // The identifier is generated by the parser, using a counter.
  irep_idt identifier() const
  {
    return get(ID_identifier);
  }

protected:
  // use base_type instead
  using type_with_subtypet::subtype;
};

/*! \brief Cast a generic typet to a \ref verilog_enum_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilog_enum_typet.
 *
 * \param type Source type
 * \return Object of type \ref verilog_enum_typet
 *
 * \ingroup gr_std_types
*/
inline const verilog_enum_typet &to_verilog_enum_type(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_enum);
  return static_cast<const verilog_enum_typet &>(type);
}

/*! \copydoc to_verilog_enum_type(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_enum_typet &to_verilog_enum_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_enum);
  return static_cast<verilog_enum_typet &>(type);
}

#endif
