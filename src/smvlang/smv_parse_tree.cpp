/*******************************************************************\

Module: SMV Parse Tree

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_parse_tree.h"

/*******************************************************************\

Function: smv_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_parse_treet::swap(smv_parse_treet &smv_parse_tree)
{
  smv_parse_tree.modules.swap(modules);
  smv_parse_tree.enum_set.swap(enum_set);
}

/*******************************************************************\

Function: smv_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_parse_treet::clear()
{
  modules.clear();
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string to_string(smv_parse_treet::modulet::itemt::item_typet i)
{
  switch(i)
  {
  case smv_parse_treet::modulet::itemt::ASSIGN_CURRENT:
    return "ASSIGN CURRENT";
  case smv_parse_treet::modulet::itemt::ASSIGN_INIT:
    return "ASSIGN INIT";
  case smv_parse_treet::modulet::itemt::ASSIGN_NEXT:
    return "ASSIGN NEXT";
  case smv_parse_treet::modulet::itemt::INVAR:    return "INVAR";
  case smv_parse_treet::modulet::itemt::TRANS:    return "TRANS";
  case smv_parse_treet::modulet::itemt::INIT:     return "INIT";
  case smv_parse_treet::modulet::itemt::CTLSPEC:
    return "SPEC";
  case smv_parse_treet::modulet::itemt::LTLSPEC:
    return "LTLSPEC";
  case smv_parse_treet::modulet::itemt::FAIRNESS: return "FAIRNESS";
  case smv_parse_treet::modulet::itemt::DEFINE:
    return "DEFINE";
  case smv_parse_treet::modulet::itemt::ENUM:
    return "ENUM";
  case smv_parse_treet::modulet::itemt::VAR:
    return "VAR";

  default:;
  }
  
  return "";
}
