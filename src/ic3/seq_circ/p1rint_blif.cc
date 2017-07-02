/******************************************************

Module:  Printing circuit in the BLIF format (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com
******************************************************/
#include <iostream>
#include <fstream>
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
void print_blif(std::ofstream &Out_str,Circuit *N)
{
  
  // print first three comands 
  circ_print_header(Out_str,N);
 //  print out the gates

  for (size_t i=0; i < N->Gate_list.size();i++)
   {Gate &G = N->Gate_list[i];
     switch (G.gate_type)
       {case INPUT: 
            break;
       case LATCH:
	 print_latch(Out_str,N,G);
         break;
       case GATE:
         if (G.func_type == CONST) print_const(Out_str,N,G);
         else  print_gate(Out_str,N,G);
         break;
       default: 
         assert(false); // we shouldn't reach this line
       }
   }
 //  print out the '.end' command
 Out_str << ".end\n";

}/* end of function print_blif */


/*=======================================

      P R I N T _ L A T C H

=======================================*/
void print_latch(std::ofstream &Out_str,Circuit *N,Gate &G)
{
 Out_str << ".latch ";
 print_names(Out_str,N,G.Fanin_list);
 Out_str << " ";
 fprint_name(Out_str,G.Gate_name);

 assert((G.init_value >= 0) && (G.init_value <= 4));
 if (G.init_value == 0)  Out_str <<  " 0\n";
 else if (G.init_value == 1) Out_str << " 1\n";
 else if (G.init_value == 2) Out_str << " 2\n";
 else Out_str << " 3\n";


}/*end of function print_latch */


/*==========================================

        P R I N T _ N A M E S

===========================================*/
void print_names(std::ofstream &Out_str,Circuit *N,CUBE &gates)
{int count=0;

  for (size_t i=0; i < gates.size();i++) {
    count++;
    Gate &G =  N->Gate_list[gates[i]];
    fprint_name(Out_str,G.Gate_name);
    if (i != gates.size()-1) // put a space if it is not the last name
      Out_str << " ";
  // every NAMES_MAX names we add the extension symbol 
  // unless it is the last name 
  if ((count == NAMES_MAX) && (i != gates.size()-1)) {
    count = 0; 
    Out_str << "\\\n";
  }
}

} /* end of function print_names */

/*=================================

          P R I N T _ C U B E 

=================================*/
void print_cube(std::ofstream &Out_str,CUBE &C,int ninputs)
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
        Out_str << "0";
        break;
      case 1:
        Out_str << "1";
        break;
      case 2:
        Out_str << "-";
        break;
     }
   }
}/* end of function print_cube */
/*=======================================

      P R I N T _ C O N S T

=======================================*/
void print_const(std::ofstream &Out_str,Circuit *N,Gate &G)
{
  // print the .names command
 Out_str << ".names ";
 fprint_name(Out_str,G.Gate_name);
 Out_str << "\n";
 
 if (G.F.size() == 1) Out_str << "1\n";

}/* end of function print_const */
/*=======================================

      P R I N T _ G A T E

=======================================*/
void print_gate(std::ofstream &Out_str,Circuit *N,Gate &G)
{
  // print the .names command
 Out_str << ".names ";
 print_names(Out_str,N,G.Fanin_list);
 Out_str << " ";
 fprint_name(Out_str,G.Gate_name);
 Out_str << "\n";

 // print the cubes of the ON-set

 for (size_t i=0; i < G.F.size();i++) {
   print_cube(Out_str,G.F[i],G.ninputs);
   Out_str << " 1\n";
 }
 // print the cubes of the OFF-set
 for (size_t i=0; i < G.R.size();i++) {
   print_cube(Out_str,G.R[i],G.ninputs);
   Out_str << " 0\n";
 }   


}/* end of function print_gate */

/*=====================================

   C I R C _ P R I N T _ H E A D E R

 The function prints the head
 of a blif file
======================================*/
void circ_print_header(std::ofstream &Out_str,Circuit *N)
{
// print out the '.model' command
 Out_str << ".model ";
 if (N->Circuit_name.size() > 0)
   fprint_name(Out_str,N->Circuit_name);
 else
   Out_str << "seq_circ";
 Out_str << "\n";

 // print out the '.inputs' command
 Out_str << ".inputs ";
 print_names(Out_str,N,N->Inputs);
 Out_str << "\n";
 // print out the '.outputs' command
 Out_str << ".outputs ";
 print_names(Out_str,N,N->Outputs);
 Out_str << "\n";
}/* end of function circ_print_header */


