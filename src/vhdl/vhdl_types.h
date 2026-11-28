/*******************************************************************\

Module: VHDL Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Types
///
/// There are three kinds of types in the VHDL front-end:
///
/// 1. The type definitions and subtype indications produced by the
///    parser (the classes at the end of this file). The type checker
///    resolves these into
///
/// 2. the VHDL types: vhdl_enumeration_typet, vhdl_integer_typet,
///    vhdl_array_typet and vhdl_record_typet. These carry the names of
///    the type and of its base type, and the constraint, and are the
///    types of the expressions produced by the type checker and
///    consumed by the synthesis. They are mapped by vhdl_lowering to
///
/// 3. CBMC types: boolean, bit and std_(u)logic become bool, integer
///    types signedbv(32), arrays of bit or std_(u)logic unsignedbv
///    (signedbv for signed), other arrays array types, enumeration
///    types enumeration types, and records struct types.

#ifndef CPROVER_VHDL_VHDL_TYPES_H
#define CPROVER_VHDL_VHDL_TYPES_H

#include <util/mp_arith.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <optional>

/// the direction of an index range or a slice
enum class vhdl_directiont
{
  TO,
  DOWNTO
};

irep_idt to_irep_id(vhdl_directiont);
vhdl_directiont to_vhdl_direction(irep_idt);

/// the index range of an array type, or the range of an integer
/// subtype (IEEE 1076-2008 5.2.1)
struct vhdl_ranget
{
  mp_integer left, right;
  vhdl_directiont direction;

  mp_integer low() const
  {
    return direction == vhdl_directiont::TO ? left : right;
  }

  mp_integer high() const
  {
    return direction == vhdl_directiont::TO ? right : left;
  }

  /// the number of elements
  mp_integer length() const
  {
    auto l = high() - low() + 1;
    return l < 0 ? 0 : l;
  }

  /// the position of the given VHDL index, counting from 0 for the
  /// element with the lowest index
  mp_integer position(const mp_integer &index) const
  {
    return index - low();
  }

  std::string to_string() const;
};

/// The base class of the VHDL types. The identifier is the name of the
/// type or subtype, in lower case; the base type name identifies the
/// type for type compatibility (IEEE 1076-2008 5.1).
class vhdl_typet : public typet
{
public:
  irep_idt name() const
  {
    return get(ID_identifier);
  }

  irep_idt base_name() const
  {
    return get(ID_vhdl_base_type);
  }

  /// a subtype declaration gives the type a new name
  void set_name(irep_idt _name)
  {
    set(ID_identifier, _name);
  }

protected:
  vhdl_typet(irep_idt _id, irep_idt _name) : typet(std::move(_id))
  {
    set(ID_identifier, _name);
    set(ID_vhdl_base_type, _name);
  }
};

/// IEEE 1076-2008 5.2.2: an enumeration type. The elements are the
/// literals, in order: identifiers in lower case, or character literals
/// with their quotes, e.g. '1', which keeps them apart from identifiers
/// and case sensitive. boolean, bit and std_ulogic are enumeration
/// types.
class vhdl_enumeration_typet : public vhdl_typet
{
public:
  vhdl_enumeration_typet(irep_idt _name, irept::subt _elements)
    : vhdl_typet(ID_vhdl_enumeration, _name)
  {
    add(ID_elements).get_sub() = std::move(_elements);
  }

  const irept::subt &elements() const
  {
    return find(ID_elements).get_sub();
  }

  /// IEEE 1076-2008 5.2.2.1: the position number of a literal
  std::optional<std::size_t> position(irep_idt literal) const;

  /// the literal for a character, with its quotes
  static irep_idt character_literal(char ch)
  {
    return std::string("'") + ch + "'";
  }

  static bool is_character_literal(irep_idt literal)
  {
    return !literal.empty() && literal[0] == '\'';
  }

  irep_idt literal(std::size_t position) const
  {
    return elements()[position].id();
  }
};

inline const vhdl_enumeration_typet &to_vhdl_enumeration_type(const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_enumeration);
  return static_cast<const vhdl_enumeration_typet &>(type);
}

/// IEEE 1076-2008 5.2.3: an integer type or subtype, with its range
class vhdl_integer_typet : public vhdl_typet
{
public:
  vhdl_integer_typet(irep_idt _name, const vhdl_ranget &);

  vhdl_ranget range() const;
  void set_range(const vhdl_ranget &);
};

inline const vhdl_integer_typet &to_vhdl_integer_type(const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_integer);
  return static_cast<const vhdl_integer_typet &>(type);
}

/// IEEE 1076-2008 5.3.2: a one-dimensional array type or subtype, with
/// an element type, an index subtype, and, when constrained, an index
/// range. The index subtype is an integer subtype, e.g., natural for
/// bit_vector; its left bound and direction give the index range of
/// values whose range is not given by the context (9.3.2, 9.2.5).
class vhdl_array_typet : public vhdl_typet
{
public:
  /// an unconstrained array type, e.g., array (positive range <>) of bit
  vhdl_array_typet(
    irep_idt _name,
    typet _element_type,
    const vhdl_integer_typet &_index_type)
    : vhdl_typet(ID_vhdl_array, _name)
  {
    add(ID_element_type) = std::move(_element_type);
    add(ID_vhdl_index_type) = _index_type;
  }

  /// a constrained array type, e.g., array (1 to 4) of bit; the index
  /// subtype is integer with the given range
  vhdl_array_typet(irep_idt _name, typet _element_type, const vhdl_ranget &);

  const typet &element_type() const
  {
    return static_cast<const typet &>(find(ID_element_type));
  }

  const vhdl_integer_typet &index_type() const
  {
    return static_cast<const vhdl_integer_typet &>(find(ID_vhdl_index_type));
  }

  bool is_constrained() const
  {
    return !get(ID_vhdl_direction).empty();
  }

  /// the index range; the array must be constrained
  vhdl_ranget range() const;
  void set_range(const vhdl_ranget &);

  /// IEEE 1076-2008 9.3.2, 9.2.5: the index range of a value with the
  /// given number of elements when the context does not give one: it
  /// starts at the left bound of the index subtype and has its direction
  vhdl_ranget range_for_length(const mp_integer &) const;

  mp_integer length() const
  {
    return range().length();
  }

  /// the same array type, without the index constraint
  vhdl_array_typet unconstrained() const;
};

inline const vhdl_array_typet &to_vhdl_array_type(const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_array);
  return static_cast<const vhdl_array_typet &>(type);
}

/// IEEE 1076-2008 5.3.3: a record type; the components are stored as
/// for struct types
class vhdl_record_typet : public vhdl_typet
{
public:
  using componentt = struct_union_typet::componentt;
  using componentst = struct_union_typet::componentst;

  vhdl_record_typet(irep_idt _name, componentst _components)
    : vhdl_typet(ID_vhdl_record, _name)
  {
    components() = std::move(_components);
  }

  const componentst &components() const
  {
    return (const componentst &)(find(ID_components).get_sub());
  }

  componentst &components()
  {
    return (componentst &)(add(ID_components).get_sub());
  }

  bool has_component(irep_idt) const;
  const componentt &get_component(irep_idt) const;
};

inline const vhdl_record_typet &to_vhdl_record_type(const typet &type)
{
  PRECONDITION(type.id() == ID_vhdl_record);
  return static_cast<const vhdl_record_typet &>(type);
}

// The predefined types (IEEE 1076-2008 16.3) and the types of the
// IEEE packages std_logic_1164 and numeric_std.
vhdl_enumeration_typet vhdl_boolean_type();
vhdl_enumeration_typet vhdl_bit_type();
vhdl_enumeration_typet vhdl_std_ulogic_type();
/// std_logic is a subtype of std_ulogic with the same values
vhdl_enumeration_typet vhdl_std_logic_type();
vhdl_integer_typet vhdl_integer_type();
/// a subtype of integer with the given range
vhdl_integer_typet vhdl_integer_type(const vhdl_ranget &);
vhdl_integer_typet vhdl_natural_type();
vhdl_integer_typet vhdl_positive_type();
/// bit_vector, std_logic_vector, std_ulogic_vector, unsigned, signed
vhdl_array_typet vhdl_unconstrained_array_type(irep_idt name);
/// one of the above, constrained to the given range
vhdl_array_typet vhdl_vector_type(irep_idt name, const vhdl_ranget &);
/// the given array type, constrained to the given range
vhdl_array_typet
vhdl_constrained_array_type(const vhdl_array_typet &, const vhdl_ranget &);

/// true for std_logic, std_ulogic and bit
bool is_vhdl_scalar_bit_type(const typet &);
/// true for constrained arrays of bit or std_(u)logic, i.e., the types
/// that are mapped to bit-vectors
bool is_vhdl_vector_type(const typet &);
/// true for array types without an index constraint, e.g., bit_vector
bool is_unconstrained_array(const typet &);
/// true for the arrays of numeric_std, unsigned and signed
bool is_vhdl_numeric_vector_type(const typet &);
/// true for integer, its subtypes, and user-defined integer types
bool is_vhdl_integer_type(const typet &);
/// true for the types of literals whose type depends on the context:
/// the universal types, aggregates, and overloaded enumeration literals
bool is_vhdl_universal_type(const typet &);

/// true if the types are the same VHDL type, possibly different
/// subtypes (IEEE 1076-2008 5.1)
bool vhdl_types_compatible(const typet &, const typet &);

/// IEEE 1076-2008 5.2.1: the base type of a scalar subtype, which is
/// the type of the result of the predefined operators. For integer
/// types, this has the range of integer. Other types are returned
/// unchanged.
typet vhdl_base_type(const typet &);

/// the VHDL type, with its constraint, for messages
std::string vhdl_type_to_string(const typet &);

/// a constant of a VHDL integer type; the value is kept in decimal
constant_exprt vhdl_integer_constant(const mp_integer &, const typet &);
mp_integer vhdl_integer_value(const constant_exprt &);

/// IEEE 1076-2008 6.3: a subtype indication, i.e., a type mark with an
/// optional range constraint (e.g. integer range 0 to 7) or index
/// constraint (e.g. std_logic_vector(7 downto 0)), as produced by the
/// parser
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
