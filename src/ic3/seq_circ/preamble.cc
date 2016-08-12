/******************************************************

Module: Reading in a sequential circuit specified in the
        BLIF formula (Part 1)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"

/* ===========================================

            S E T _ M O D E L

   The function sets model name. It returns 0 if
   buff does not contain the '.model' command or 
   the model name is wrong.

   Otherwise, it returns 1.

   ===========================================*/
int set_model(CCUBE buf,Circuit *N)
{int i;
  CCUBE name;

  i=0;
  if (compare(buf,".model",i)==0)
    return(0); 


  // skip  blanks after the command text
  i=str_size(".model"); 
  skip_blanks(buf,i);

  
  // copy the model name
 
  copy_name(buf,name,i);

  if (name.size()==0)
    return(0);

  N->Circuit_name = name;
  return(1);

}/* end of function set_model */


/*==========================================

  A D D _ I N P U T

  The function adds a new input to circuit N

  ===========================================*/
void add_input(CCUBE &name,Circuit *N,int inp_gate_num)
{Gate I;

  init_gate_fields(I);

  //    Form an input node

  I.func_type = BUFFER;
  I.gate_type = INPUT;
  I.flags.active = 1; // mark this input as active 
  I.flags.output = 0;
  I.flags.transition = 0;
  I.flags.output_function = 0;
  I.flags.feeds_latch = 0;
  I.level_from_inputs = 0; // set the topological level to 0
  I.Gate_name = name;
  I.inp_feeds_latch = false;

 
  //   Add it to the circuit
   
  N->Inputs.push_back(inp_gate_num);
  N->ninputs++; // increment the number of inputs
  N->Gate_list.push_back(I); // add input 
  N->Pin_list[name] = inp_gate_num;
 

}/* end of function add_input */




/*===========================================

  C R E A T E _ I N P U T S

  The function creates inputs. It returns 0 if
  buff does not contain the '.inputs' command or 
  an input's name is wrong.

  Otherwise, it returns 1.

  ===========================================*/
int create_inputs(CCUBE &buf,Circuit *N)
{int i;
  CCUBE name;

  i = 0;
  if (compare(buf,".inputs",i)== 0)
    return(0); 

  // skip  blanks after the command text
  i = str_size(".inputs");
  skip_blanks(buf,i);

  while (1)
    {name.clear();
      copy_name(buf,name,i);
      if (name.size() == 0)
	break;
      add_input(name,N,N->ninputs);
      skip_blanks(buf,i);
    }

  return(1);
} /* end of function create_inputs */


/*=======================================================

      C R E A T E _ O U T P U T S

  The function creates an array of names output nodes. 
  It returns 0 if buff does not contain the '.outputs' 
  command or an output's name is wrong.

  Otherwise, it returns 1.

  =========================================================*/
int create_outputs(CCUBE &buf,CDNF &Out_names)
{int i;
  CCUBE name;

  i = 0;
  if (compare(buf,".outputs",i)== 0)
    return(0); 

  // skip  blanks after the command text
  i=str_size(".outputs");
  skip_blanks(buf,i);
 
  while (true) {
    name.clear();
    copy_name(buf,name,i);
    if (name.size() == 0)
      break;
    Out_names.push_back(name);
    skip_blanks(buf,i);
  }
  return(1);
} /* end of function create_outputs */

