/******************************************************

Module: Reading circuit from a BLIF or AIG file
        (part 5)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <queue>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>
#include "Solver.h"
#include "SimpSolver.h"
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"
#include "m0ic3.hh"

/*=========================================

      U P D _ G A T E _ C O N S T R S

  =======================================*/
void CompInfo::upd_gate_constrs(aiger_and &Aig_gate,CUBE &Gate_inds) 
{
  assert(Gate_inds.size() == 3);
  upd_gate_constr_tbl(Aig_gate.rhs0,Gate_inds[0]);
  upd_gate_constr_tbl(Aig_gate.rhs1,Gate_inds[1]);
  upd_gate_constr_tbl(Aig_gate.lhs,Gate_inds[2]);

} /* end of function upd_gate_constrs */

/*=====================================================

      U P D _ G A T E _ C O N S T R _ T B L

   Returns 

    0 if neither 'lit' nor '~lit' are constrained
    1 if 'lit' or '~lit' are constrained and 'Constr_gates'
      had no entry for 'gate_ind'
    2 if 'Constr_gates' has an entry for 'gate_ind'

  =====================================================*/
int CompInfo::upd_gate_constr_tbl(int lit,int gate_ind)
{

  if (Constr_gates.find(gate_ind) != Constr_gates.end())
    return(2);

  

  int fnd_lit;
  bool found = check_constr_lits(fnd_lit,lit);
     
  if (!found) return(0);
  assert(lit > 1);

  if (fnd_lit & 1) Constr_gates[gate_ind].neg_lit = 1;
  else Constr_gates[gate_ind].neg_lit = 0;
  
  return(1);

} /* end of function proc_lit_if_constr */

/*=====================================

   S T O R E _ C O N S T R A I N T S

  ======================================*/
void CompInfo::store_constraints(aiger &A)
{

  if (constr_flag == false) return;

  for (int i=0; i < A.num_constraints; i++)
    Aig_clits.insert(A.constraints[i].lit);

} /* end of function store_constraints */

/*======================================

       F O R M _ L A T C H _ N A M E

 ======================================*/
void form_latch_name(CCUBE &Latch_name,aiger_symbol &S) 
{
  char Buff[MAX_NAME];
  sprintf(Buff,"l%d",S.lit);
  conv_to_vect(Latch_name,Buff);
} /* end of function form_latch_name */

/*========================================================

       R E A D _ N A M E S _ O F _ L A T C H E S

  =========================================================*/
void read_names_of_latches(NamesOfLatches &Latches,char *fname)
{

  FILE *fp = fopen(fname,"r");

  if (fp ==NULL) {
    printf("file %s open failure\n",fname);
    exit(1);}

  while (true) {

    CCUBE Buff;
    int ret_val = read_string(fp,Buff);
    if (ret_val == -1) break;
    int res = parse_string(Buff);
    if (res == 0) continue; // not  '.latch' or '.names' commands   
    assert(res == 1); // assert that Buff contains command '.latch'
    CCUBE Lname;
    extract_latch_name(Lname,Buff);
    Latches[Lname] = 0; 
  }

  fclose(fp);

} /* end of function read_names_of_latches */




/*===================================

        P A R S E _ S T R I N G

  returns 
   1  if Buff contains '.latch'
   0   Otherwise

  =================================*/
int parse_string(CCUBE &Buff) 
{

  if (Buff.size() == 0) return(0);
  char Command[7];

  for (int i=0; i < 6; i++) 
    Command[i] = Buff[i];
  Command[6] = 0;

  if (strcmp(Command,".latch") == 0) return(1);

  return(0);

} /* end of function parse_string */


/*===============================================

    P R I N T _ N A M E S _ O F _ L A T C H E S

  ===============================================*/
void print_names_of_latches(NamesOfLatches &Latches) 
{

  NamesOfLatches::iterator pnt;

  for (pnt = Latches.begin(); pnt != Latches.end(); pnt++) {
    CCUBE A = pnt->first;
    print_name(&A);
    printf("\n"); 
  }
} /* end of function print_names_of_latches */
