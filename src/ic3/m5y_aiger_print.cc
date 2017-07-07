/******************************************************

Module: Printing circuit in text version of aiger format  
        (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include <fstream>

#include <ebmc/ebmc_base.h>
#include <util/message.h>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"

#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*===========================================

     P R I N T _ A I G E R _ C O N S T R S

  ============================================*/
void CompInfo::print_aiger_constrs(std::ofstream &Out_str)
{

  ConstrGates::iterator pnt;

  for (pnt = Constr_gates.begin(); pnt!= Constr_gates.end(); pnt++) {
    int gate_ind = pnt->first;
    char neg_lit = pnt->second.neg_lit;
    int lit = find_aiger_lit2(gate_ind,neg_lit);
    Out_str << lit << "\n";
  }
} /* end of function print_aiger_constrs */

/*============================================

     P R I N T _ A I G E R _ G A T E S

  ==========================================*/
void CompInfo::print_aiger_gates(std::ofstream &Out_str,DNF &Gates)
{

  for (size_t i=0; i < Gates.size(); i++) {
    CUBE &C = Gates[i];
    assert(C.size() == 3);
    Out_str << C[0] << " " << C[1] << " " << C[2] << "\n";
  }

} /* end of function print_aiger_gates */

/*===============================

       A D D _ T R I P L E T

  ==============================*/
void CompInfo::add_triplet(DNF &Gates,int olit,int lit0,int lit1)
{

  CUBE C;
  C.push_back(olit); C.push_back(lit0); C.push_back(lit1);
  Gates.push_back(C);

} /* end of function add_triplet */



/*=========================================

     F I N D _ M A X _ A I G E R _ V A R

  =========================================*/
int CompInfo::find_max_aiger_var(DNF &Gates)
{

  int max_lit = -1;
  for (size_t i=0; i < Gates.size(); i++) {
    CUBE &C = Gates[i];
    for (size_t j=0; j < C.size(); j++) 
      if (C[j] > max_lit) max_lit = C[j];
  }

  assert(max_lit >= 0);
  if (max_lit & 1) max_lit--;
  return(max_lit >> 1);
} /* end of function find_max_aiger_var */



/*==========================================

      P R I N T _ A I G E R _ O U T P U T

  ==========================================*/
void CompInfo::print_aiger_output(std::ofstream &Out_str,DNF &Gates,int out_ind)
{
  CUBE &C  = Gates[out_ind];
  assert(C.size() == 3);
  int lit = C[0];  

  if (const_true_prop) { // make sure that the output is always 0
    assert(C[1] == C[2]);
    if (C[1] == 1) lit++; // negate the conjunction of constants 1
  }

  if (const_false_prop) { // make sure that the output is always 1
    if ((C[1] == 0) || (C[2] == 0)) // at least one of the inputs is 0
      lit++;
  }

  Out_str << lit << "\n";
  
} /* end of function print_aiger_output */

/*=============================================

    A D D _ A I G E R _ A N D _ G A T E

  ============================================*/
void CompInfo::add_aiger_and_gate(DNF &Gates,int gate_ind)
{

  Gate &G = N->get_gate(gate_ind);
  assert(G.Polarity.back() == 0);
  int olit = find_aiger_lit1(gate_ind,0);
  int lit0 = find_aiger_lit1(G.Fanin_list[0],G.Polarity[0]);
  int lit1 = find_aiger_lit1(G.Fanin_list[1],G.Polarity[1]);

  add_triplet(Gates,olit,lit0,lit1);
 
 
} /* end of function add_aiger_and_gate */

/*=============================================

    A D D _ A I G E R _ B U F F E R

  ============================================*/
void CompInfo::add_aiger_buffer(DNF &Gates,int gate_ind)
{

  Gate &G = N->get_gate(gate_ind);
  assert(G.Polarity.back() == 0);
  int olit = find_aiger_lit1(gate_ind,0);
  int ilit = find_aiger_lit1(G.Fanin_list[0],G.Polarity[0]);

  add_triplet(Gates,olit,ilit,ilit);
 
} /* end of function add_aiger_buffer */

/*=================================

  P R I N T _ F U N C _ T Y P E

  ================================*/
void CompInfo::print_func_type(Gate &G,unsigned message_level) 
{

  messaget::mstreamt &Ms = M->get_mstream(message_level);
  switch (G.func_type) {
  case CONST:
    Ms << "CONST";
    break;
  case BUFFER:
    Ms << "BUFFER";
    break;
  case AND:
    Ms << "AND";
    break;
  case OR:
    Ms << "OR";
    break;
  case TRUTH_TABLE:
    Ms << "TRUTH_TABLE";
    break;
  case COMPLEX:
    Ms << "COMPLEX";
    break;
  default:
    Ms <<"wrong value of func_type\n";
    throw(ERROR1);
  }

  Ms << M->eom;

} /* end of function print_func_type */

