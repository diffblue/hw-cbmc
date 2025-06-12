/*******************************************************************\

Module: SMV Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_TYPES_H
#define CPROVER_SMV_TYPES_H

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

#endif // CPROVER_SMV_TYPES_H
