/******************************************************

Module: Printing circuit in text version of aiger format  
        (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

#include <ebmc/ebmc_base.h>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"

#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

/*====================================

 P R I N T _ A I G E R _ F O R M A T

  ====================================*/
void CompInfo::print_aiger_format()
{

  int num_consts;
  int num_buffs;
  check_circuit(num_buffs,num_consts);
  assert(num_consts <= 2);
  std::string full_name;
  assert(strlen(out_file) > 0);
  full_name = out_file;
  full_name += ".aag";

  FILE *fp = fopen(full_name.c_str(),"w");
  assert(fp!= NULL);
  
  DNF Gates;
  int out_ind = form_aiger_gates(Gates);

  int max_var = find_max_aiger_var(Gates);
  print_aiger_header(fp,max_var,Gates.size());
  print_aiger_inps(fp);
  print_aiger_latches(fp);
  print_aiger_output(fp,Gates,out_ind);
  print_aiger_constrs(fp);
  print_aiger_gates(fp,Gates);
  fclose(fp);
} /* end of function print_aiger_format */

/*=======================================

     F O R M _ A I G E R _ G A T E S

  =======================================*/
int CompInfo::form_aiger_gates(DNF &Gates)
{

  int ind = -1;
  assert(N->Outputs.size() == 1);
  size_t out_gate_ind = N->Outputs[0];
  for (size_t i=0; i < N->Gate_list.size(); i++) {
    Gate &G = N->Gate_list[i];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
    if (G.func_type == CONST) continue;
    assert(G.ninputs <= 2);
    if (i == out_gate_ind)
      ind = Gates.size();
    if (G.func_type == AND) {
       add_aiger_and_gate(Gates,i);
       continue;
    }
    assert(G.func_type == BUFFER);
    add_aiger_buffer(Gates,i);
  }
  assert(ind >= 0);
  return(ind);

} /* end of function form_aiger_gates */
/*=================================

    F I N D _ A I G E R _ L I T 1

  ================================*/
int CompInfo::find_aiger_lit1(int gate_ind,char polarity)
{

  Gate &G = N->get_gate(gate_ind);

  if (G.func_type == CONST) {
    if (G.F.size() > 0) return(1);
    else {
      assert(F.size() == 0);
      return(0);
    }
  }

  int lit = (gate_ind+1) << 1;
  if (polarity) return(lit+1);
  else return(lit);

} /* end of function find_aiger_lit1 */

/*=================================

    F I N D _ A I G E R _ L I T 2

  ================================*/
int CompInfo::find_aiger_lit2(int gate_ind,char polarity)
{


  int lit = (gate_ind+1) << 1;
  if (polarity) return(lit+1);
  else return(lit);

} /* end of function find_aiger_lit2 */

/*========================================

    P R I N T _ A I G E R _ L A T C H E S

  ======================================*/
void CompInfo::print_aiger_latches(FILE *fp)
{

  for (size_t i=0; i < N->Latches.size(); i++) {
    int gate_ind = N->Latches[i];
    int lit = (gate_ind+1) << 1;
    fprintf(fp,"%d ",lit);
    Gate &G = N->get_gate(gate_ind);
    assert(G.Fanin_list.size() == 1);
    int next_lit = find_aiger_lit1(G.Fanin_list[0],0);
    fprintf(fp,"%d ",next_lit);
    if (G.init_value == 2) {
      fprintf(fp,"%d\n",lit);
      continue;}
    assert((G.init_value == 0) || (G.init_value == 1));
    fprintf(fp,"%d\n",G.init_value);
  }

} /* end of function print_aiger_latches */


/*========================================

    P R I N T _ A I G E R _ I N P S

  ======================================*/
void CompInfo::print_aiger_inps(FILE *fp)
{

  for (size_t i=0; i < N->Inputs.size(); i++) {
    int gate_ind = N->Inputs[i];
    fprintf(fp,"%d\n",(gate_ind+1)<<1);
  }

} /* end of function print_aiger_inps */


/*========================================

    P R I N T _ A I G E R _ H E A D E R

  ======================================*/
void CompInfo::print_aiger_header(FILE *fp,int max_var,int num_gates)
{

  fprintf(fp,"aag ");

  fprintf(fp,"%d ",max_var); 
  fprintf(fp,"%d ",N->ninputs);
  fprintf(fp,"%d ",N->nlatches);
  fprintf(fp,"1 ");
  fprintf(fp,"%d",num_gates);
  if (Constr_gates.size() == 0)  fprintf(fp,"\n");
  else fprintf(fp," 0 %d\n",(int) Constr_gates.size());
} /* end of function print_aiger_header*/




/*==============================

    C H E C K _ C I R C U I T

  ===============================*/
void CompInfo::check_circuit(int &num_buffs,int &num_consts)
{

  num_consts = 0;
  num_buffs = 0;
  for (size_t i=0; i < N->Gate_list.size(); i++) {
    Gate &G = N->Gate_list[i];
    if (G.gate_type == INPUT) continue;
    if (G.gate_type == LATCH) continue;
    assert(G.gate_type == GATE);
    bool cond = (G.func_type == AND);
    cond |= (G.func_type == BUFFER);
    cond |= (G.func_type == CONST);
    if (!cond) {
      p();
      print_func_type(G);
      exit(100);
    } 

    if (G.func_type == CONST) num_consts++;
    if (G.func_type == BUFFER) num_buffs++;
    
    if (G.ninputs != 2) {
      bool cond = (i == N->Gate_list.size()-2);
      cond |= (G.func_type == BUFFER);
      cond |= (G.func_type == CONST);
      if (!cond)      {
        p();
	printf("i = %d\n",i);
	printf("N->Gate_list.size() = %d\n",(int) N->Gate_list.size());
	printf("G.ninputs = %d\n",G.ninputs);
	exit(100);
      }
    }
  }
  
} /* end of function check_circuit */
