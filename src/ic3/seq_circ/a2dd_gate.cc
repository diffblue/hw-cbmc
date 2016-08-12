/******************************************************

Module: Adding a new gate (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <assert.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"


/*==========================================================


  A S S I G N _ I N P U T _ P I N _ N U M B E R 1

  The function assigns a numeric lable to an input of a gate.
  The function either puts name into the map pin_list
  (if it is new) and returns its key, or just returns
  the key (name is already in  pin_list).  If 'name' is new
  a new gate is added to gate_list
  =========================================================*/
int assign_input_pin_number1(std::map<CCUBE,int> &pin_list,
			     CCUBE &name,GCUBE &gate_list)
{int pin_num;
  Gate G;

  if (pin_list.find(name) == pin_list.end()) {
    init_gate_fields(G);
    pin_num = pin_list.size(); // new pin 
    pin_list[name] = pin_num;
    G.flags.active = 0;
    G.gate_type = UNDEFINED;
    gate_list.push_back(G); // add one more gate 
  }
  else /* an 'old' pin */
    pin_num=pin_list[name]; // add to input list the current gate input      
     
  return(pin_num);

} /* end of function assign_input_pin_number1 */

/*========================================================


  A S S I G N _ O U T P U T _ P I N _ N U M B E R

  The function assigns a numeric lable to the output of a
  gate. The function either puts name into the map pin_list
  (if it is new) and returns its key, or just returns
  the key (name is already in  pin_list).  If 'name' is new
  a new gate is added to gate_list
  =========================================================*/
int assign_output_pin_number(std::map<CCUBE,int> &pin_list,
			     CCUBE &name,GCUBE &gate_list,bool latch)
{int pin_num;
  Gate G;


  if (pin_list.find(name) == pin_list.end()) {  
    init_gate_fields(G);
    pin_num = pin_list.size(); // new pin 
    pin_list[name] = pin_num;
    G.flags.active = 0;
    G.gate_type = UNDEFINED;   
    if (latch) {
      G.latch_feeds_latch = false;  
      G.gate_type = LATCH;
    }
    gate_list.push_back(G); // add one more gate 
  }
  else { /* an 'old' pin */
    pin_num=pin_list[name]; // add to input list the current gate input      
    if (gate_list[pin_num].flags.active == 1) {
      printf("two gates have the same name "); print_name1(name); printf("\n");
      exit(1);         
    }
  }
  return(pin_num);

} /* end of function assign_output_pin_number */
/*=========================================================

        S T A R T _ G A T E

  The function initializes a new gate and adds it
  to the circuit N. 
  It returns in gate_ind the numer index assigned to the
  output variables of the gate (which is also the position
  of this gate in N.gate_list)
  =============================================================*/
void start_gate(CCUBE &buf,Circuit *N,int &gate_ind)
{CCUBE name;

  CDNF Pin_names;
  // skip  blanks after the command text
 
  int i=str_size(".names");
  skip_blanks(buf,i);

  //
  //  store the  gate pins
  //
  while (true) {
    name.clear();
    copy_name(buf,name,i);
    if (name.size() == 0)
      break;
    Pin_names.push_back(name);
    skip_blanks(buf,i);
  }
 
 
  // process the output name
  int pin_num = assign_output_pin_number(N->Pin_list,Pin_names.back(),N->Gate_list,false);
 
  N->ngates++; // increment the number of gates 
  gate_ind = pin_num;

  //  process  the  input names
  for (int j=0; j < Pin_names.size()-1;j++) {
    int pin_num = assign_input_pin_number1(N->Pin_list,Pin_names[j],N->Gate_list);
    Gate &G =  N->Gate_list[gate_ind];
    G.Fanin_list.push_back(pin_num);   
  }

  /*-------------------------------------
    Form a gate node
    ---------------------------------------*/ 
  // gate has more than one pin?
  {
    Gate &G =   N->Gate_list[gate_ind];
    G.ninputs = Pin_names.size()-1;

    if (G.ninputs == 0)  {
      N->Constants.push_back(gate_ind);
      N->nconstants++;
    }
  }
 
  Gate &G =   N->Gate_list[gate_ind];
  G.gate_type = UNDEFINED;
  G.level_from_inputs = -1; // initialize topological level
  G.level_from_outputs = -1;
  G.flags.active = 1; // mark G as an active  gate
  G.flags.output = 0;
  G.flags.transition = 0;
  G.flags.output_function = 0;
  G.flags.feeds_latch = 0;
  G.Gate_name =  Pin_names.back(); 


}/* end of function start_gate */

/*============================================

      A D D _ N E W _ C U B E

  The function processes new cube and adds it 
  either to the on-set or off-set

  =============================================*/
void add_new_cube(CCUBE &buf,Circuit *N,int &gate_ind)
{CCUBE cube_descr;
  int i=0;
  CUBE C;

  Gate &G=  N->Gate_list[gate_ind];
  if (G.ninputs == 0) {// a constant
    assert((G.F.size() == 0) && (G.R.size() == 0));
    CUBE C;
    G.F.push_back(C); //adding an empty cube to F makes the gate constant 1
    return;
  }
 
  i=0; skip_blanks(buf,i); // skip blanks 

  //
  // process cube description
  //
  for (; i < buf.size();i++)
    switch(buf[i])
      {case '0':
	  C.push_back(-1*(i+1));
	  break;
      case '1':
	C.push_back(i+1);
	break;
      case '-':
	break;
      case ' ':
      case '\t':
	goto NEXT;
      default:
	error_message(WRONG_SYNTAX,buf);
	exit(syn_error);
      }
 NEXT:
  skip_blanks(buf,i); // skip blank(s)
  //
  // add C either to the On-set or the Off-set

 
  switch (buf[i])
    {case '1':
	G.F.push_back(C);
	break;
    case '0':
      G.R.push_back(C);
      break;
    default: 
      error_message(WRONG_SYNTAX,buf);
      exit(syn_error);
    }  

}/* end of function add_new_cube */
