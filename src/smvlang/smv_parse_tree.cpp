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

std::string to_string(smv_parse_treet::modulet::elementt::element_typet i)
{
  switch(i)
  {
  case smv_parse_treet::modulet::elementt::ASSIGN_CURRENT:
    return "ASSIGN CURRENT";
  case smv_parse_treet::modulet::elementt::ASSIGN_INIT:
    return "ASSIGN INIT";
  case smv_parse_treet::modulet::elementt::ASSIGN_NEXT:
    return "ASSIGN NEXT";
  case smv_parse_treet::modulet::elementt::INVAR:
    return "INVAR";
  case smv_parse_treet::modulet::elementt::TRANS:
    return "TRANS";
  case smv_parse_treet::modulet::elementt::INIT:
    return "INIT";
  case smv_parse_treet::modulet::elementt::CTLSPEC:
    return "SPEC";
  case smv_parse_treet::modulet::elementt::LTLSPEC:
    return "LTLSPEC";
  case smv_parse_treet::modulet::elementt::FAIRNESS:
    return "FAIRNESS";
  case smv_parse_treet::modulet::elementt::DEFINE:
    return "DEFINE";
  case smv_parse_treet::modulet::elementt::ENUM:
    return "ENUM";
  case smv_parse_treet::modulet::elementt::IVAR:
    return "IVAR";
  case smv_parse_treet::modulet::elementt::VAR:
    return "VAR";

  default:;
  }
  
  return "";
}
