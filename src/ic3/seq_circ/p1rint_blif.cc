/******************************************************

Module:  Printing circuit in the BLIF format (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com
******************************************************/
#include <iostream>
#include <list>
#include <vector>
#include <set>
#include <map>
#include <string>
#include <algorithm>
#include <queue>

#include <stdio.h>
#include <assert.h>
#include "dnf_io.hh"
#include "ccircuit.hh"

/*====================================

         P R I N T _ B L I F

 Prints out circuit N in the blif format
====================================*/
void print_blif(FILE *fp,Circuit *N)
{
  
  // print first three comands 
  circ_print_header(fp,N);
 //  print out the gates

  for (size_t i=0; i < N->Gate_list.size();i++)
   {Gate &G = N->Gate_list[i];
     switch (G.gate_type)
       {case INPUT: 
            break;
       case LATCH:
	 print_latch(fp,N,G);
         break;
       case GATE:
         if (G.func_type == CONST) print_const(fp,N,G);
         else  print_gate(fp,N,G);
         break;
       default: 
         assert(false); // we shouldn't reach this line
       }
   }
 //  print out the '.end' command
 fprintf(fp,".end\n");

}/* end of function print_blif */


/*=======================================

      P R I N T _ L A T C H

=======================================*/
void print_latch(FILE *fp,Circuit *N,Gate &G)
{
 fprintf(fp,".latch ");
 print_names(fp,N,G.Fanin_list);
 fprintf(fp," "); fprint_name(fp,G.Gate_name);

 assert((G.init_value >= 0) && (G.init_value <= 4));
 fprintf(fp," %d\n",G.init_value);


}/*end of function print_latch */


/*==========================================

        P R I N T _ N A M E S

===========================================*/
void print_names(FILE *fp,Circuit *N,CUBE &gates)
{int count=0;

 for (size_t i=0; i < gates.size();i++)
   {count++;
    Gate &G =  N->Gate_list[gates[i]];
    fprint_name(fp,G.Gate_name);
    if (i != gates.size()-1) // put a space if it is not the last name
       fprintf(fp," ");
// every NAMES_MAX names we add the extension symbol 
 // unless it is the last name 
    if ((count == NAMES_MAX) && (i != gates.size()-1)) 
      {count = 0; 
       fprintf(fp,"\\\n");
      }
   }

} /* end of function print_names */

/*=================================

          P R I N T _ C U B E 

=================================*/
void print_cube(FILE *fp,CUBE &C,int ninputs)
{CCUBE L;

 for (int i=0; i < ninputs; i++)
   L.push_back(2);

 for (size_t i=0; i < C.size();i++)
   if (C[i] < 0)
     L[(-1*C[i])-1]=0;
   else
     L[C[i]-1]=1;
    
 for (size_t i=0; i < L.size();i++)
   {switch (L[i])
     {case 0:
        fprintf(fp,"0");
        break;
      case 1:
        fprintf(fp,"1");
        break;
      case 2:
        fprintf(fp,"-");
        break;
     }
   }
}/* end of function print_cube */
/*=======================================

      P R I N T _ C O N S T

=======================================*/
void print_const(FILE *fp,Circuit *N,Gate &G)
{
  // print the .names command
 fprintf(fp,".names ");
 fprint_name(fp,G.Gate_name);
 fprintf(fp,"\n");
 
 if (G.F.size() == 1) fprintf(fp,"1\n");

}/* end of function print_const */
/*=======================================

      P R I N T _ G A T E

=======================================*/
void print_gate(FILE *fp,Circuit *N,Gate &G)
{
  // print the .names command
 fprintf(fp,".names ");
 print_names(fp,N,G.Fanin_list);
 fprintf(fp," "); fprint_name(fp,G.Gate_name);
 fprintf(fp,"\n");

 // print the cubes of the ON-set

 for (size_t i=0; i < G.F.size();i++) {
   print_cube(fp,G.F[i],G.ninputs);
   fprintf(fp," 1\n");
 }
 // print the cubes of the OFF-set
 for (size_t i=0; i < G.R.size();i++) {
   print_cube(fp,G.R[i],G.ninputs);
   fprintf(fp," 0\n");
 }   


}/* end of function print_gate */

/*=====================================

   C I R C _ P R I N T _ H E A D E R

 The function prints the head
 of a blif file
======================================*/
void circ_print_header(FILE *fp,Circuit *N)
{
// print out the '.model' command
 fprintf(fp,".model ");
 fprint_name(fp,N->Circuit_name);
 fprintf(fp,"\n");

 // print out the '.inputs' command
 fprintf(fp,".inputs ");
 print_names(fp,N,N->Inputs);
 fprintf(fp,"\n");
 // print out the '.outputs' command
 fprintf(fp,".outputs ");
 print_names(fp,N,N->Outputs);
 fprintf(fp,"\n");
}/* end of function circ_print_header */


