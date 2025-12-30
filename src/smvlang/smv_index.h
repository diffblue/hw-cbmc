/*******************************************************************\

Module: SMV Parse Tree Index

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_SMV_INDEX_H
#define CPROVER_SMV_INDEX_H

#include "smv_parse_tree.h"

#include <set>

class smv_indext
{
public:
  smv_indext() = default;
  explicit smv_indext(smv_parse_treet &);

  using module_listt = smv_parse_treet::module_listt;

  // map from module base names into the module list
  using module_mapt =
    std::unordered_map<irep_idt, module_listt::iterator, irep_id_hash>;
  module_mapt module_map;

  std::set<irep_idt> enum_names;
};

#endif // CPROVER_SMV_INDEX_H
