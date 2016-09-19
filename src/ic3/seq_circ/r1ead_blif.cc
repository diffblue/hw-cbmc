/******************************************************

Module: Reading in a sequential circuit specified in the
        BLIF formula (Part 2)

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

/*=================================================

  R E A D _ B L I F

  The function reads in the specified specified
  by  'fp' and returns a pointer to a circuit
  ==================================================*/
Circuit  *read_blif(FILE *fp,NamesOfLatches &Latches,reader_state &r)
{CCUBE buf;


  Circuit *N = create_circuit(); // create a circuit 

  // ------------------------------------------
  // read in the .model command 
  // ------------------------------------------

  while (true) {
    // read the next line (or lines if there is the extention sign) 
    // and strip off the comments 
    if (read_string(fp,buf) == -1)  {
      error_message(WRONG_EOF,buf);  // eof occured too early 
      exit(eof_error);
    }
    
    if (blank_line(buf))
      continue;
    if (set_model(buf,N)==0) {
      error_message(WRONG_SYNTAX,buf);
      exit(syn_error);
    }
    else   break;
  }

  // 
  // read in the .inputs command 
  //
  while (true) {
    // read the next line (or lines if there is the extention sign) 
    // and strip off the comments 
    if (read_string(fp,buf) == -1) {
      error_message(WRONG_EOF,buf);  // eof occured too early 
      exit(eof_error);
    }
    if (blank_line(buf))
      continue;
    if (create_inputs(buf,N)==0) {
      error_message(WRONG_SYNTAX,buf);
      exit(syn_error);
    }
    else  break;
  }

  //
  // read in the .outputs command 
  //
  CDNF Out_names;
  while (true) {
    // read the next line (or lines if there is the extention sign) and strip off the comments 
    if (read_string(fp,buf) == -1) 
      {error_message(WRONG_EOF,buf);  // eof occured too early 
	exit(eof_error);
      }
    if (blank_line(buf)) // an empty line or a comment
      continue;
    if (create_outputs(buf,Out_names)==0) {
      error_message(WRONG_SYNTAX,buf);
      exit(syn_error);
    }
    else break;
  }

 
  //
  //    READ IN THE BODY
  //

  int gate_ind;
  while (true) {
   // read the next line (or lines if there is the extention sign)
   // and strip off the comments 
      if (read_string(fp,buf) == -1)
	if (r.ignore_missing_end)
          break;
	else {
  // eof occured before seeing the '.end' line 
  // (-1 is returned by read_string only  if buf is empty)
	  error_message(WRONG_EOF,buf); 
	    exit(eof_error);
	  }
      if (blank_line(buf)) // an empty line or a comment
	continue;
      if (buf[0] == '.') { // a command line 
	if (r.unfinished_gate)
	  {finish_gate(N,gate_ind); // finish processing the current gate
	    r.unfinished_gate = false;
	  }
      }
      else {
      // not a command, buf contains next cube description 
	assert(r.unfinished_gate);
	add_new_cube(buf,N,gate_ind);
	continue;
      }
      Command_type reply = identify_command(buf);
      switch (reply) {
      case DOT_NAMES: // start a new gate
        {r.unfinished_gate = true;
	  start_gate(buf,N,gate_ind);
	  continue;
	}
      case DOT_END:  // '.end' line?
	goto FINISH_CIRCUIT;
      case DOT_LATCH:
	{int answer = add_latch(buf,Latches,N,gate_ind);
	  if (answer == 0)
	    {error_message(WRONG_SYNTAX,buf);
	      exit(syn_error);
	    }
	  continue;
	}
      case WRONG:
	{error_message(WRONG_SYNTAX,buf);
	  exit(syn_error);
        }
      default: assert(false); // shouldn't reach this line
      }
      
  
    }
 
 FINISH_CIRCUIT:
  add_spec_buffs(N);
  fill_fanout_lists(N);
  if (r.check_fanout_free_inputs)  check_fanout_free_inputs(N,r);
  assign_gate_type(N,Out_names,r.rem_dupl_opt);

  // assign topological levels and other flags
  assign_levels_from_inputs(N);
  set_trans_output_fun_flags(N);
  set_feeds_latch_flag(N,r.ignore_errors,r.rem_dupl_opt);

  assign_levels_from_outputs(N);
  return(N);
} /* end of function read_blif */


/*==================================

  A D D _ S P E C _ B U F F S

  =================================*/
void add_spec_buffs(Circuit *N) 
{

  //  printf("add_spec_buffs\n");
  if (N->num_spec_buffs == 0) return;

  gen_spec_buff_name(N);

  for (int i=0; i < N->num_spec_buffs; i++) 
    add_one_spec_buff(N,i);

} /* end of function add_spec_buffs */


