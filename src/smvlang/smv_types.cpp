/*******************************************************************\

Module: SMV Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_types.h"

#include <set>

smv_enumeration_typet::smv_enumeration_typet(
  const std::vector<irep_idt> &element_ids)
  : typet(ID_smv_enumeration)
{
  auto &sub = elements_sub();
  for(auto &element_id : element_ids)
    sub.push_back(irept{element_id});
}

std::vector<irep_idt> smv_enumeration_typet::elements() const
{
  std::vector<irep_idt> result;

  auto &elements_sub = find(ID_elements).get_sub();

  result.reserve(elements_sub.size());

  for(auto &e : elements_sub)
    result.push_back(e.id());

  return result;
}

bool smv_enumeration_typet::is_subset_of(
  const smv_enumeration_typet &other) const
{
  // This is quadratic.
  for(auto &element1 : elements())
  {
    bool found = false;
    for(auto &element2 : other.elements())
      if(element1 == element2)
      {
        found = true;
        break;
      }

    if(!found)
      return false;
  }

  return true;
}

smv_enumeration_typet type_union(
  const smv_enumeration_typet &e_type1,
  const smv_enumeration_typet &e_type2)
{
  if(e_type2.is_subset_of(e_type1))
    return e_type1;

  if(e_type1.is_subset_of(e_type2))
    return e_type2;

  // make union
  std::set<irep_idt> enum_set;

  for(auto &e : e_type1.elements())
    enum_set.insert(e);

  for(auto &e : e_type2.elements())
    enum_set.insert(e);

  // turn into vector
  std::vector<irep_idt> elements;

  elements.reserve(enum_set.size());

  for(auto &e : enum_set)
    elements.push_back(e);

  return smv_enumeration_typet{std::move(elements)};
}
