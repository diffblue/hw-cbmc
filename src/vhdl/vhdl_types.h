/*******************************************************************\

Module: VHDL Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Types
///
/// The VHDL-specific types produced by the parser. They are resolved
/// during type checking.

#ifndef CPROVER_VHDL_VHDL_TYPES_H
#define CPROVER_VHDL_VHDL_TYPES_H

#include <util/std_expr.h>
#include <util/std_types.h>

/// IEEE 1076-2008 6.3: a subtype indication, i.e., a type mark with an
/// optional range constraint (e.g. integer range 0 to 7) or index
/// constraint (e.g. std_logic_vector(7 downto 0))
class vhdl_subtype_indicationt : public typet
{
public:
  explicit vhdl_subtype_indicationt(exprt _type_mark)
    : typet(ID_vhdl_subtype_indication)
  {
    add(ID_name) = std::move(_type_mark);
  }

  /// a name, possibly a selected name
  const exprt &type_mark() const
  {
    return static_cast<const exprt &>(find(ID_name));
  }

  /// nil, a vhdl_range_exprt, or a range attribute
  const exprt &range_constraint() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_range_constraint));
  }

  void range_constraint(exprt _range)
  {
    add(ID_vhdl_range_constraint) = std::move(_range);
  }

  /// the discrete ranges of the index constraint, one per dimension
  const irept::subt &index_constraint() const
  {
    return find(ID_vhdl_index_constraint).get_sub();
  }

  irept::subt &index_constraint()
  {
    return add(ID_vhdl_index_constraint).get_sub();
  }

  bool has_constraint() const
  {
    return range_constraint().is_not_nil() ||
           find(ID_vhdl_index_constraint).is_not_nil();
  }
};

inline const vhdl_subtype_indicationt &
to_vhdl_subtype_indication(const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_subtype_indication);
  return static_cast<const vhdl_subtype_indicationt &>(type);
}

/// IEEE 1076-2008 5.2.2: an enumeration type definition; the elements
/// are the literals, identifiers or character literals
class vhdl_enumeration_type_definitiont : public typet
{
public:
  vhdl_enumeration_type_definitiont() : typet(ID_enumeration)
  {
    add(ID_elements);
  }

  const irept::subt &elements() const
  {
    return find(ID_elements).get_sub();
  }

  irept::subt &elements()
  {
    return add(ID_elements).get_sub();
  }
};

/// IEEE 1076-2008 5.2.3: an integer type definition, range ...
class vhdl_integer_type_definitiont : public typet
{
public:
  explicit vhdl_integer_type_definitiont(exprt _range) : typet(ID_range)
  {
    add(ID_range) = std::move(_range);
  }

  const exprt &range() const
  {
    return static_cast<const exprt &>(find(ID_range));
  }
};

/// IEEE 1076-2008 5.3.2: an array type definition. The index
/// constraint has one entry per dimension, which is a discrete range,
/// or ID_vhdl_unconstrained with the index type for array (t range <>).
class vhdl_array_type_definitiont : public typet
{
public:
  explicit vhdl_array_type_definitiont(typet _element_type) : typet(ID_array)
  {
    add(ID_vhdl_index_constraint);
    add(ID_element_type) = std::move(_element_type);
  }

  const irept::subt &index_constraint() const
  {
    return find(ID_vhdl_index_constraint).get_sub();
  }

  irept::subt &index_constraint()
  {
    return add(ID_vhdl_index_constraint).get_sub();
  }

  const typet &element_type() const
  {
    return static_cast<const typet &>(find(ID_element_type));
  }
};

/// IEEE 1076-2008 5.3.3: a record type definition; the elements are
/// element declarations, each with declarators and a type
class vhdl_record_type_definitiont : public typet
{
public:
  vhdl_record_type_definitiont() : typet(ID_struct)
  {
    add(ID_elements);
  }

  const irept::subt &elements() const
  {
    return find(ID_elements).get_sub();
  }

  irept::subt &elements()
  {
    return add(ID_elements).get_sub();
  }
};

#endif // CPROVER_VHDL_VHDL_TYPES_H
