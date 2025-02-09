/*******************************************************************\

Module: Verilog Types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPES_H
#define CPROVER_VERILOG_TYPES_H

#include <util/bitvector_types.h>
#include <util/ieee_float.h>

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

/*! \brief Cast a generic typet to a \ref to_be_elaborated_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * to_be_elaborated_typet.
 *
 * \param type Source type
 * \return Object of type \ref to_be_elaborated_typet
 *
 * \ingroup gr_std_types
*/
inline const to_be_elaborated_typet &to_to_be_elaborated_type(const typet &type)
{
  PRECONDITION(type.id() == ID_to_be_elaborated);
  return static_cast<const to_be_elaborated_typet &>(type);
}

/*! \copydoc to_to_be_elaborated_type(const typet &)
 * \ingroup gr_std_types
*/
inline to_be_elaborated_typet &to_to_be_elaborated_type(typet &type)
{
  PRECONDITION(type.id() == ID_to_be_elaborated);
  return static_cast<to_be_elaborated_typet &>(type);
}

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

  explicit inline verilog_signedbv_typet(std::size_t width)
    : bitvector_typet(ID_verilog_signedbv, width)
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

  explicit inline verilog_unsignedbv_typet(std::size_t width)
    : bitvector_typet(ID_verilog_unsignedbv, width)
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

  typet lower() const
  {
    typet type = ieee_float_spect::double_precision().to_type();
    type.set(ID_C_verilog_type, ID_verilog_real);
    return type;
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

  typet lower() const
  {
    typet type = ieee_float_spect::single_precision().to_type();
    type.set(ID_C_verilog_type, ID_verilog_shortreal);
    return type;
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

  typet lower() const
  {
    typet type = ieee_float_spect::double_precision().to_type();
    type.set(ID_C_verilog_type, ID_verilog_realtime);
    return type;
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

  typet lower() const
  {
    typet type = signedbv_typet{width()};
    type.set(ID_C_verilog_type, ID_verilog_shortint);
    return type;
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

  typet lower() const
  {
    typet type = signedbv_typet{width()};
    type.set(ID_C_verilog_type, ID_verilog_int);
    return type;
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

  typet lower() const
  {
    typet type = signedbv_typet{width()};
    type.set(ID_C_verilog_type, ID_verilog_longint);
    return type;
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

  typet lower() const
  {
    typet type = signedbv_typet{width()};
    type.set(ID_C_verilog_type, ID_verilog_byte);
    return type;
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

    const source_locationt &source_location() const
    {
      return static_cast<const source_locationt &>(find(ID_C_source_location));
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

class verilog_type_referencet : public typet
{
public:
  // This comes in two flavors: a reference to the type
  // of a given type, or of a given expression.
  const exprt &expression_op() const
  {
    if(get_sub().size() == 1)
      return static_cast<const exprt &>(get_sub().front());
    else
      return static_cast<const exprt &>(get_nil_irep());
  }

  const typet &type_op() const
  {
    return static_cast<const typet &>(find(ID_type_arg));
  }
};

/*! \brief Cast a generic typet to a \ref verilog_type_referencet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * verilog_type_referencet.
 *
 * \param type Source type
 * \return Object of type \ref verilog_type_referencet
 *
 * \ingroup gr_std_types
*/
inline const verilog_type_referencet &
to_verilog_type_reference(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_type_reference);
  return static_cast<const verilog_type_referencet &>(type);
}

/*! \copydoc to_verilog_type_reference(const typet &)
 * \ingroup gr_std_types
*/
inline verilog_type_referencet &to_verilog_type_reference(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_type_reference);
  return static_cast<verilog_type_referencet &>(type);
}

/// The SystemVerilog struct/union type
class verilog_struct_union_typet : public struct_union_typet
{
public:
  verilog_struct_union_typet(
    irep_idt __id,
    bool __is_packed,
    componentst _components)
    : struct_union_typet(__id, std::move(_components))
  {
    is_packed(__is_packed);
  }

  bool is_packed() const
  {
    return get_bool(ID_verilog_packed);
  }

  void is_packed(bool __is_packed)
  {
    return set(ID_verilog_packed, __is_packed);
  }
};

/// The SystemVerilog union type
class verilog_union_typet : public verilog_struct_union_typet
{
public:
  verilog_union_typet(bool __is_packed, componentst _components)
    : verilog_struct_union_typet(ID_union, __is_packed, std::move(_components))
  {
  }
};

/// \brief Cast a typet to a \ref verilog_union_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// verilog_union_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref verilog_union_typet
inline const verilog_union_typet &to_verilog_union_type(const typet &type)
{
  PRECONDITION(type.id() == ID_union);
  return static_cast<const verilog_union_typet &>(type);
}

/// \copydoc to_union_type(const typet &)
inline verilog_union_typet &to_verilog_union_type(typet &type)
{
  PRECONDITION(type.id() == ID_union);
  return static_cast<verilog_union_typet &>(type);
}

/// a pointer type
class verilog_chandle_typet : public typet
{
public:
  inline verilog_chandle_typet() : typet(ID_verilog_chandle)
  {
  }

  bv_typet encoding() const
  {
    return bv_typet{32};
  }

  constant_exprt null_expr() const;
};

/// \brief Cast a typet to a \ref verilog_chandle_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// verilog_chandle_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref verilog_chandle_typet
inline const verilog_chandle_typet &to_verilog_chandle_type(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_chandle);
  return static_cast<const verilog_chandle_typet &>(type);
}

/// \copydoc to_chandle_type(const typet &)
inline verilog_chandle_typet &to_verilog_chandle_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_chandle);
  return static_cast<verilog_chandle_typet &>(type);
}

/// The SystemVerilog event type
class verilog_event_typet : public typet
{
public:
  verilog_event_typet() : typet(ID_verilog_event)
  {
  }

  constant_exprt null_expr() const;

  bv_typet encoding() const
  {
    return bv_typet{32};
  }
};

/// \brief Cast a typet to a \ref verilog_event_typet
///
/// This is an unchecked conversion. \a type must be known to be \ref
/// verilog_event_typet. Will fail with a precondition violation if type
/// doesn't match.
///
/// \param type: Source type.
/// \return Object of type \ref verilog_event_typet
inline const verilog_event_typet &to_verilog_event_type(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_event);
  return static_cast<const verilog_event_typet &>(type);
}

/// \copydoc to_event_type(const typet &)
inline verilog_event_typet &to_verilog_event_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_event);
  return static_cast<verilog_event_typet &>(type);
}

/// A typedef
class verilog_typedef_typet : public typet
{
public:
  explicit verilog_typedef_typet(const irep_idt &_identifier)
    : typet(ID_typedef_type)
  {
    identifier(_identifier);
  }

  void identifier(const irep_idt &identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }
};

/// Cast a generic typet to a \ref verilog_typedef_typet. This is an unchecked
/// conversion. \a type must be known to be \ref verilog_typedef_typet.
/// \param type: Source type
/// \return Object of type \ref verilog_typedef_typet
inline const verilog_typedef_typet &to_verilog_typedef_type(const typet &type)
{
  PRECONDITION(type.id() == ID_typedef_type);
  return static_cast<const verilog_typedef_typet &>(type);
}

/// \copydoc to_verilog_typedef_type(const typet &)
inline verilog_typedef_typet &to_verilog_typedef_type(typet &type)
{
  PRECONDITION(type.id() == ID_typedef_type);
  return static_cast<verilog_typedef_typet &>(type);
}

/// package::type
class verilog_package_scope_typet : public type_with_subtypest
{
public:
  irep_idt package_base_name() const
  {
    return subtypes()[0].id();
  }

  const typet &typedef_type() const
  {
    return subtypes()[1];
  }

  static void
  check(const typet &, const validation_modet = validation_modet::INVARIANT);
};

/// Cast a generic typet to a \ref verilog_package_scope_typet. This is an unchecked
/// conversion. \a type must be known to be \ref verilog_package_scope_typet.
/// \param type: Source type
/// \return Object of type \ref verilog_package_scope_typet
inline const verilog_package_scope_typet &
to_verilog_package_scope_type(const typet &type)
{
  PRECONDITION(type.id() == ID_verilog_package_scope);
  verilog_package_scope_typet::check(type);
  return static_cast<const verilog_package_scope_typet &>(type);
}

/// \copydoc to_verilog_typedef_type(const typet &)
inline verilog_package_scope_typet &to_verilog_package_scope_type(typet &type)
{
  PRECONDITION(type.id() == ID_verilog_package_scope);
  verilog_package_scope_typet::check(type);
  return static_cast<verilog_package_scope_typet &>(type);
}

#endif
