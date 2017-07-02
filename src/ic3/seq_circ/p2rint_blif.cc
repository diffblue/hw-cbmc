/******************************************************

Module:  Printing circuit in the BLIF format (Part 2)

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
#include "s0hared_consts.hh"

/*=======================================

         P R I N T _ B L I F 2

 In contrast to 'print_blif', this
 function guarantees that all latches
 are printed out one by one
========================================*/
void print_blif2(std::ofstream &Out_str,Circuit *N)
{
  
  // print first three commands 
  circ_print_header(Out_str,N);
 
  //  print out latches
  CUBE &Latches = N->Latches;
  for (size_t i=0; i < Latches.size(); i++)  {
    Gate &G = N->get_gate(Latches[i]);
    print_latch(Out_str,N,G);
  }
 
  for (size_t i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    switch (G.gate_type)
      {case INPUT: 
       case LATCH:
	break;
      case GATE:
	if (G.func_type == CONST) print_const(Out_str,N,G);
	else  print_gate(Out_str,N,G);
	break;
      case UNDEFINED: 
	p();
	std::cout << "type of gate ";
	print_name(&G.Gate_name);
	std::cout << " is UNDEFINED\n";
	throw(ERROR1);
      default:
	assert(false);
      }
  }

 //  print out the '.end' command
  Out_str << ".end\n";

}/* end of function print_blif2 */

/*========================

   P R I N T _ B L I F 3

==========================*/
void print_blif3(const char *fname, Circuit *N)
{

  std::ofstream Out_str(fname,std::ios::out);
  if (!Out_str) {
    std::cout << "cannot open file " << std::string(fname) << "\n";
    throw(ERROR2);}
  
  print_blif2(Out_str,N);
  Out_str.close();

} /* end of function print_blif3 */
