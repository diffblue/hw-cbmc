/*******************************************************************\

Module: SMV Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_TYPES_H
#define CPROVER_SMV_TYPES_H

#include <util/expr.h>
#include <util/mp_arith.h>
#include <util/type.h>

#include <set>

/// The SMV enumerated type
class smv_enumeration_typet : public typet
{
public:
  smv_enumeration_typet() : typet(ID_smv_enumeration)
  {
  }

  explicit smv_enumeration_typet(const std::set<irep_idt> &);

  bool is_subset_of(const smv_enumeration_typet &) const;

  // the ordering does not matter; this makes a copy
  std::vector<irep_idt> elements() const;

  subt &elements_sub()
  {
    return add(ID_elements).get_sub();
  }

  const subt &elements_sub() const
  {
    return find(ID_elements).get_sub();
  }

  // order elements by <
  void normalize();
};

/// compute the union of the given enumeration types
smv_enumeration_typet
type_union(const smv_enumeration_typet &, const smv_enumeration_typet &);

/*! \brief Cast a generic typet to a \ref smv_enumeration_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_enumeration_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_enumeration_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_enumeration_typet &to_smv_enumeration_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_enumeration);
  return static_cast<const smv_enumeration_typet &>(type);
}

/*! \copydoc to_smv_enumeration_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_enumeration_typet &to_smv_enumeration_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_enumeration);
  return static_cast<smv_enumeration_typet &>(type);
}

/// The SMV set type -- NuSMV distinguishes the boolean set, the integer set,
/// the symbolic set, and the integers-and-symbolic set.
class smv_set_typet : public type_with_subtypet
{
public:
  explicit smv_set_typet(typet subtype)
    : type_with_subtypet(ID_smv_set, std::move(subtype))
  {
  }

  const typet &element_type() const
  {
    return subtype();
  }
};

/*! \brief Cast a generic typet to a \ref smv_set_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_set_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_set_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_set_typet &to_smv_set_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_set);
  return static_cast<const smv_set_typet &>(type);
}

/*! \copydoc to_smv_set_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_set_typet &to_smv_set_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_set);
  return static_cast<smv_set_typet &>(type);
}

class smv_array_typet : public type_with_subtypet
{
public:
  smv_array_typet(mp_integer from, mp_integer to, typet subtype);

  const exprt &from() const
  {
    return static_cast<const exprt &>(find(ID_from));
  }

  exprt &from()
  {
    return static_cast<exprt &>(add(ID_from));
  }

  const exprt &to() const
  {
    return static_cast<const exprt &>(find(ID_to));
  }

  exprt &to()
  {
    return static_cast<exprt &>(add(ID_to));
  }

  const typet &element_type() const
  {
    return subtype();
  }

  typet &element_type()
  {
    return subtype();
  }
};

/*! \brief Cast a generic typet to a \ref smv_array_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_array_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_array_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_array_typet &to_smv_array_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_array);
  return static_cast<const smv_array_typet &>(type);
}

/*! \copydoc to_smv_array_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_array_typet &to_smv_array_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_array);
  return static_cast<smv_array_typet &>(type);
}

class smv_range_typet : public typet
{
public:
  smv_range_typet(mp_integer from, mp_integer to);

  const exprt &from() const
  {
    return static_cast<const exprt &>(find(ID_from));
  }

  exprt &from()
  {
    return static_cast<exprt &>(add(ID_from));
  }

  const exprt &to() const
  {
    return static_cast<const exprt &>(find(ID_to));
  }

  exprt &to()
  {
    return static_cast<exprt &>(add(ID_to));
  }
};

/*! \brief Cast a generic typet to a \ref smv_range_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_range_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_range_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_range_typet &to_smv_range_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_range);
  return static_cast<const smv_range_typet &>(type);
}

/*! \copydoc to_smv_range_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_range_typet &to_smv_range_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_range);
  return static_cast<smv_range_typet &>(type);
}

class smv_word_base_typet : public typet
{
public:
  smv_word_base_typet(irep_idt id, mp_integer width);

  const exprt &width() const
  {
    return static_cast<const exprt &>(find(ID_width));
  }

  exprt &width()
  {
    return static_cast<exprt &>(add(ID_width));
  }
};

/*! \brief Cast a generic typet to a \ref smv_word_base_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_word_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_word_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_word_base_typet &to_smv_word_base_type(const typet &type)
{
  return static_cast<const smv_word_base_typet &>(type);
}

/*! \copydoc to_smv_word_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_word_base_typet &to_smv_word_base_type(typet &type)
{
  return static_cast<smv_word_base_typet &>(type);
}

class smv_signed_word_typet : public smv_word_base_typet
{
public:
  explicit smv_signed_word_typet(mp_integer width)
    : smv_word_base_typet{ID_smv_signed_word, std::move(width)}
  {
  }
};

/*! \brief Cast a generic typet to a \ref smv_signed_word_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_signed_word_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_signed_word_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_signed_word_typet &to_smv_signed_word_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_signed_word);
  return static_cast<const smv_signed_word_typet &>(type);
}

/*! \copydoc to_smv_signed_word_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_signed_word_typet &to_smv_signed_word_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_signed_word);
  return static_cast<smv_signed_word_typet &>(type);
}

class smv_unsigned_word_typet : public smv_word_base_typet
{
public:
  explicit smv_unsigned_word_typet(mp_integer width)
    : smv_word_base_typet{ID_smv_unsigned_word, std::move(width)}
  {
  }
};

/*! \brief Cast a generic typet to a \ref smv_unsigned_word_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_unsigned_word_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_unsigned_word_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_unsigned_word_typet &
to_smv_unsigned_word_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_unsigned_word);
  return static_cast<const smv_unsigned_word_typet &>(type);
}

/*! \copydoc to_smv_unsigned_word_type(const typet &)
 * \ingroup gr_std_types
*/
inline smv_unsigned_word_typet &to_smv_unsigned_word_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_unsigned_word);
  return static_cast<smv_unsigned_word_typet &>(type);
}

/// The type used for VAR declarations that are in fact module instantiations
class smv_module_instance_typet : public typet
{
public:
  explicit smv_module_instance_typet(irep_idt _base_name)
    : typet{ID_smv_module_instance}
  {
    base_name(_base_name);
  }

  // the base name of the module that is instantiated
  irep_idt base_name() const
  {
    return get(ID_base_name);
  }

  void base_name(irep_idt _base_name)
  {
    set(ID_base_name, _base_name);
  }

  const exprt::operandst &arguments() const
  {
    return (const exprt::operandst &)get_sub();
  }

  exprt::operandst &arguments()
  {
    return (exprt::operandst &)get_sub();
  }
};

/*! \brief Cast a generic typet to a \ref smv_module_instance_typet
 *
 * This is an unchecked conversion. \a type must be known to be \ref
 * smv_module_instance_typet.
 *
 * \param type Source type
 * \return Object of type \ref smv_module_instance_typet
 *
 * \ingroup gr_std_types
*/
inline const smv_module_instance_typet &
to_smv_module_instance_type(const typet &type)
{
  PRECONDITION(type.id() == ID_smv_module_instance);
  return static_cast<const smv_module_instance_typet &>(type);
}

inline smv_module_instance_typet &to_smv_module_instance_type(typet &type)
{
  PRECONDITION(type.id() == ID_smv_module_instance);
  return static_cast<smv_module_instance_typet &>(type);
}

#endif // CPROVER_SMV_TYPES_H
