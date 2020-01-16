/******************************************************

Module: Auxiliary functions (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "s0hared_consts.hh"

/*===================================

  P R I N T _ G A T E _ N A M E

  ====================================*/
void print_gate_name(Gate &G)
{
  std::cout << "gate "; 
  print_name1(G.Gate_name);

}/* end of function print_gate_name */


/*===================================

  P R I N T _ N A M E 

  ====================================*/
void print_name(CCUBE *name)
{
  for (size_t i=0; i < name->size();i++)
    std::cout << (*name)[i];

}/* end of function print_name */

/*==========================================

  P R I N T _ G A T E _ T Y P E 

  ==========================================*/
void  print_gate_type(std::ofstream &Out_str,Circuit *N,Gate &G)
{
  switch (G.gate_type) {
  case INPUT:
    Out_str << "INPUT\n";
    break;
  case GATE:
    if (!N->output_gate(G))
      Out_str << "INTERNAL gate\n";
    else if (N->ext_gate(G))
      Out_str << "EXTERNAL gate\n";
    else if (N->ext_int_gate(G))
      Out_str << "EXTERNAL INTERANL gate\n";
    break;
  case LATCH:
    Out_str << "LATCH\n";
    break;
  case UNDEFINED:
    Out_str << "UNDEFINED gate\n";
    break;
  default:
    Out_str << "wrong switch value\n";
    throw(ERROR1);
  }


}/* end of function print_gate_type */

/*===================================

  P R I N T _ N A M E 1

  ====================================*/
void print_name1(CCUBE &name,bool cr)
{
  for (size_t i=0; i < name.size();i++)
    std::cout << name[i];

  if (cr) std::cout << "\n";

}/* end of function print_name1 */

/*========================================

  F I L L _ U P _ L E V E L S

  =========================================*/
void fill_up_levels(Circuit *N, DNF &Level_gates)
{

  GCUBE &Gate_list = N->Gate_list;
 
  for (size_t i=0; i <= N->max_levels+1; i++) {
    CUBE dummy;
    Level_gates.push_back(dummy);
  }

  for (size_t i=0; i < Gate_list.size();i++) {
    Gate &G = Gate_list[i];
    int level = G.level_from_inputs;
    if (level < 0) level = N->max_levels+1;
    Level_gates[level].push_back(i);
  }

} /* end of function fill_up_levels */

/*============================

  P R I N T _ L E V E L S

  ==============================*/
void  print_levels(Circuit *N)
{
  GCUBE &Gate_list = N->Gate_list;
  DNF Level_gates;

  fill_up_levels(N,Level_gates);

  for (size_t i=0; i < Level_gates.size(); i++) {
    std::cout << "level " << i << ":  ";
    CUBE &Level = Level_gates[i];
 
    for (size_t j=0; j < Level.size();j++) {
      Gate &G = Gate_list[Level[j]];
      print_name1(G.Gate_name);
      std::cout << "(" << G.Fanout_list.size() << ")";
      std::cout << " ";
    }
    std::cout << "\n";
  }

} /* end of function print_levels */

/*================================

  F P R I N T _ N A M E 

  ================================*/
void fprint_name(std::ofstream &Out_str,CCUBE &name)
{
  for (size_t i=0; i < name.size();i++)
    Out_str << name[i];

}/* end of function fprint_name */
