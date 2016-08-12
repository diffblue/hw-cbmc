/******************************************************

Module: CNF Generation (Part 3)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <set>
#include <map>
#include <algorithm>
#include <queue>

#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"

/*==============================

  E M P T Y _ C U B E

  This function returns 'true'
  if cube C contains opposite 
  literals. Otherwise, the 
  function returns 'false'.
  ==============================*/
bool empty_cube(CUBE &C)
{SCUBE Lits;

  for (int i=0; i < C.size(); i++) {
    if (Lits.find(-C[i]) != Lits.end())
      return(true); // empty cube
    Lits.insert(C[i]);
  }

  return(false);

} /* end of function empty_cube */

/*=========================

  F O R M _ I N D E X

  ==========================*/
int form_index(CUBE &C)
{
  int result = 0;
  for (int i=0; i < C.size();i++)
    {assert(abs(C[i]) == i+1);
      if (C[i] > 0)  result |= 1 << i;
    }

  return(result);

} /* end of function form_index */

/*================================================

  G E N _ T R A N S _ R E L

  This function is obtained from 'add_time_frame'
  and 'shift' is a "legacy parameter".

  =================================================*/
void CompInfo::gen_trans_rel(int shift)
{

  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G =  N->Gate_list[i];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
// skip the gates that are not part of the transition function
    if (G.flags.transition == 0) continue; 
    int var_ind = Gate_to_var[i]-1;
    switch (G.func_type)
      {case CONST:
	  add_const_gate_cube(Tr,i,shift);
	  break;
      case AND:   
	add_and_gate_cubes(Tr,i,shift);
	break;
      case OR:  
	add_or_gate_cubes(Tr,i,shift);
	break;
      case BUFFER: 
	add_buffer_gate_cubes(Tr,i,shift);
	break;
      case TRUTH_TABLE: 
	add_truth_table_gate_cubes(Tr,i,shift);         
	break;
      case COMPLEX: printf("complex gate\n");
	exit(1);
      default:   printf("wrong gate type\n");
	exit(1);
      }
  }

} /* end of function gen_trans_rel */

/*====================================

   P R I N T _ V A R _ I N D E X E S

====================================*/
void CompInfo::print_var_indexes(char *fname)
{


  FILE *fp = fopen(fname,"w");
  assert(fp != NULL);

  DNF topol_levels;
  
  fill_up_levels(N,topol_levels);
  CCUBE marked_vars;
  marked_vars.assign(2*N->Gate_list.size(),0);

   // print var indexes in topological order
   for (int i=0; i <= N->max_levels; i++)
     {fprintf(fp,"--------------------------------------\n");
       fprintf(fp,"topological level %d\n",i);
      CUBE &Gates = topol_levels[i];
      for (int j=0; j < Gates.size(); j++)
	{int gate_ind = Gates[j];
	 Gate &G = N->get_gate(gate_ind);
         switch (G.gate_type)
	   {case LATCH: fprintf(fp,"L: ");
	                break;
	   case INPUT: fprintf(fp,"I: ");
	                break;
	   case GATE: fprintf(fp,"G: ");
	               break;
           default: assert(false);
           }
         fprint_name(fp,G.Gate_name);
         fprintf(fp,"  %d\n",Gate_to_var[gate_ind]);
	 int tmp = Gate_to_var[gate_ind];
	 if (marked_vars[tmp] != 0)
	   {fprintf(fp,"variable %d is shared!!\n",tmp);
	   }
         marked_vars[tmp] = 1;
	}
     }
   fclose(fp);

}/* end of function print_var_indexes */
