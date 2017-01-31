/******************************************************

Module:  Printing circuit in the BLIF format (Part 2)

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

/*=======================================

         P R I N T _ B L I F 2

 In contrast to 'print_blif', this
 function guarantees that all latches
 are printed out one by one
========================================*/
void print_blif2(FILE *fp,Circuit *N)
{
  
  // print first three commands 
  circ_print_header(fp,N);
 
  //  print out latches
  CUBE &Latches = N->Latches;
  for (int i=0; i < Latches.size(); i++)  {
    Gate &G = N->get_gate(Latches[i]);
    print_latch(fp,N,G);
  }
 
  for (int i=0; i < N->Gate_list.size();i++) {
    Gate &G = N->get_gate(i);
    switch (G.gate_type)
      {case INPUT: 
       case LATCH:
	break;
      case GATE:
	if (G.func_type == CONST) print_const(fp,N,G);
	else  print_gate(fp,N,G);
	break;
      case UNDEFINED: 
	p();
	printf("type of gate ");
	print_name(&G.Gate_name);
	printf(" is UNDEFINED\n");
	exit(100);
      default:
	assert(false);
      }
  }

 //  print out the '.end' command
 fprintf(fp,".end\n");

}/* end of function print_blif2 */

/*========================

   P R I N T _ B L I F 3

==========================*/
void print_blif3(const char *fname, Circuit *N)
{

  FILE *fp = fopen(fname,"w");
  assert(fp!= NULL);
  print_blif2(fp,N);
  fclose(fp);

} /* end of function print_blif3 */
