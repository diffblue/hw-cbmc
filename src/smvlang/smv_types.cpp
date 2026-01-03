/*******************************************************************\

Module: SMV Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_types.h"

#include <util/arith_tools.h>
#include <util/mathematical_types.h>

#include <algorithm>
#include <set>

smv_enumeration_typet::smv_enumeration_typet(
  const std::set<irep_idt> &element_ids)
  : typet(ID_smv_enumeration)
{
  auto &sub = elements_sub();
  for(auto &element_id : element_ids)
    sub.push_back(irept{element_id});
}

void smv_enumeration_typet::normalize()
{
  auto &elements_sub = this->elements_sub();

  std::sort(
    elements_sub.begin(),
    elements_sub.end(),
    [](const irept &a, const irept &b) { return a.id() < b.id(); });
}

std::vector<irep_idt> smv_enumeration_typet::elements() const
{
  std::vector<irep_idt> result;

  auto &elements_sub = this->elements_sub();

  result.reserve(elements_sub.size());

  for(auto &e : elements_sub)
    result.push_back(e.id());

  return result;
}

bool smv_enumeration_typet::is_subset_of(
  const smv_enumeration_typet &other) const
{
  std::set<irep_idt> other_elements;
  auto &other_elements_sub = other.elements_sub();

  for(auto &element : other_elements_sub)
    other_elements.insert(element.id());

  for(auto &element : elements_sub())
  {
    if(other_elements.find(element.id()) == other_elements.end())
      return false;
  }

  return true;
}

smv_array_typet::smv_array_typet(mp_integer from, mp_integer to, typet subtype)
  : type_with_subtypet{ID_smv_array, std::move(subtype)}
{
  this->from() = from_integer(from, integer_typet{});
  this->to() = from_integer(to, integer_typet{});
}

smv_range_typet::smv_range_typet(mp_integer from, mp_integer to)
  : typet{ID_smv_range}
{
  this->from() = from_integer(from, integer_typet{});
  this->to() = from_integer(to, integer_typet{});
}

smv_word_base_typet::smv_word_base_typet(irep_idt id, mp_integer width)
  : typet{id}
{
  this->width() = from_integer(width, integer_typet{});
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

  return smv_enumeration_typet{enum_set};
}
