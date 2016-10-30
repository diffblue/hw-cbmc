/******************************************************

Module: Functions called to complete creation of a gate

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <stdio.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"


/*==============================================

  S E T _ I N P U T _ P O L A R I T Y

  C is a unit cube of either F or R. The function
  sets the  polarity of the variable of C depending
  on whether C contains the positive or negative literal
  of it.
  ================================================*/
void set_input_polarity(CUBE &C,Gate &G)
{if (C[0] > 0)
    G.Polarity.push_back(0); // direct input 
  else
    G.Polarity.push_back(1); //  inverted input 
}/* end of function set_input_polarity */

/*===============================================


  F I N I S H _ C O N S T A N T


  ==============================================*/
void finish_constant(Gate &G)
{
  G.func_type = CONST;
  G.level_from_inputs = 0;

}/* end of function finish_constant */
/*========================================

     F I N I S H _ B U F F E R

  The function fills up the polarities
  and sets the function  type
  =========================================*/
void finish_buffer(Gate &G)
{G.func_type = BUFFER;

  DNF &F = G.F;
  DNF &R = G.R;

  if ((F.size()+ R.size()) != 1) {
    printf("wrong buffer\n");
    std::cout << G.Gate_name << std::endl;
    printf("F.size() = %d\n",(int) F.size());
    printf("R.size() = %d\n",(int) R.size());
    exit(100);
  }

  // direct output
  if (F.size() == 1) {
    set_input_polarity(F[0],G);
    G.Polarity.push_back(0); // direct output
    return;
  }
  // inverted output
 
  set_input_polarity(R[0],G);
  G.Polarity.push_back(1); // inverted  output

} /* end of function finish_buffer */
/*===================================================

     
       C O R R E C T _ D N F

  The function returns 1 if all cubes of F are unit
  and all cubes are different. Otherwise it returns 0
  ===================================================*/
int correct_dnf(DNF &F)
{CCUBE mark(F.size());
  int var;

  for (int i=0; i < F.size();i++)
    mark[i] = 0;

  for (int i=0; i < F.size();i++) {
    CUBE &C= F[i];
    if (C.size() != 1)
      return(0);
    var = abs(C[0])-1;
    if (mark[var]==1)
      return(0); // the same variable appears in two different cubes
    mark[var]=1;
  }
  return(1);
} /* end of function correct_dnf */
/*============================================

  O R _ G A T E

  The function returns 1 if G is an 
  'OR' gate. Otherwise it returns 0
  =============================================*/
int or_gate(Gate &G)
{DNF &F = G.F;
  DNF &R = G.R;

  if ((F.size()!= 0) && (R.size()!=0))
    return(0);

  if (F.size()!= 0)
    if (correct_dnf(F))
      return(1);
    else
      return(0);
 
  if (correct_dnf(R))
    return(1);
  else
    return(0);


}/* end of function and_gate */

/*====================================

  F I N I S H _ O R _ G A T E

  The function fills up the polarities 
  and sets the function  type
  ======================================*/
void finish_or_gate(Gate &G)
{G.func_type = OR;

  
  // direct output
  DNF &F1=G.F;
  if (F1.size() > 0) {
    for (int i=0; i < F1.size();i++)
      set_input_polarity(F1[i],G);
    G.Polarity.push_back(0); 
    return;
  }

  // inverted output
  
  DNF &R1= G.R;
  if (R1.size() > 0) {
    for (int i=0; i < R1.size();i++)
      set_input_polarity(R1[i],G);
    G.Polarity.push_back(1); 
    return;
  }
}/* end of function finish_or_gate */

/*========================================

      A N D _ G A T E

  The function returns 1 if G is 
  an 'AND' gate. Otherwise it returns 0

  ========================================*/
int and_gate(Gate &G)
{ DNF &F = G.F;
  DNF &R = G.R; 

  if ((F.size() > 1 ) || (R.size() > 1))
    return(0);

  if ((F.size() + R.size()) != 1)
    return(0);

  if (F.size()!= 0)
    if (F[0].size() == G.ninputs) // the only cube of F  has all the literals
      return(1);
    else
      return(0);
 
  if (R[0].size() == G.ninputs) // the only cube of R has all the literals 
    return(1);
  else
    return(0);

}/* end of function and_gate */

/*=====================================

  F I N I S H _ A N D  _ G A T E

  The function fills up the polarities 
  and sets the function  type 
  =====================================*/ 
void finish_and_gate(Gate &G)
{G.func_type = AND;

 
  // direct output

  DNF &F1= G.F;
  if (F1.size() > 0) {
    CUBE &C = F1[0];
      for (int i=0; i < C.size();i++)
	if (C[i] > 0)
	  G.Polarity.push_back(0);
	else
	  G.Polarity.push_back(1);
      G.Polarity.push_back(0); 
    }

 
  // inverted  output

  DNF &R1= G.R;
  if (R1.size() > 0) {
    CUBE &C = R1[0];
      for (int i=0; i < C.size();i++)
	if (C[i] > 0)
	  G.Polarity.push_back(0);
	else
	  G.Polarity.push_back(1);
      G.Polarity.push_back(1); 
    }

}/* end of function finish_and_gate */

/*========================================

       T R U T H _ T A B L E

  ASSUMPTIONS:
  No cube of the ON-SET contains duplicate
  literals.

  ========================================*/
bool truth_table(Gate &G)
{
  DNF &F = G.F;
  
  for (int i=0; i < F.size();i++)
    if (F[i].size() != G.ninputs) return(false);  

  return(true);

} /* end of function truth_table */

/*========================================

  F I N I S H _ U N K N O W N _ G A T E

  =========================================*/
void finish_unknown_gate(Gate &G)
{
  if (truth_table(G)) G.func_type = TRUTH_TABLE;
  else G.func_type = COMPLEX;

}/* end of function finish_unknown_gate */

/*==================================================

      F I N I S H _ G A T E

  The function finishes gate description.
  In particular it determines gate type and fills up
  the polarities
  ==================================================*/
void finish_gate(Circuit *N,int &gate_ind)
{

  Gate &G=  N->Gate_list[gate_ind];

  if (G.ninputs == 0) {
     finish_constant(G);
     return;
    }

  // is it a BUFFER?
  if (G.ninputs == 1) {
    finish_buffer(G);
    return;
  }
 
  // is it an OR gate?
  if (or_gate(G)) {
    finish_or_gate(G);
    return;
  }
 
  // is it an AND gate? 

  if (and_gate(G)) {
    finish_and_gate(G);
    return;
  }
 
  // it is a complex gate  or a truth_table
  finish_unknown_gate(G);


}/* end of function finish_gate */
