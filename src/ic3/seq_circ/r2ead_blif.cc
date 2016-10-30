/******************************************************

Module: Reading in a sequential circuit specified in the
        BLIF formula (Part 3)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"

/*=========================================

  A D D _ O N E _ S P E C _ B U F F

  ==========================================*/
void add_one_spec_buff(Circuit *N,int ind) 
{
  int gate_ind = spec_buff_gate_ind(N,ind);
  start_spec_buff(N,gate_ind);
  add_spec_buff_cube(N,gate_ind);
  finish_spec_buff(N,gate_ind);

} /* end of function add_one_spec_buff */

/*====================================

  N A M E _ C L A S H

  This function returns 'true' if
  there is clash in names 'Root_name'
  and 'Gate_name'. A clash takes place
  if 'Gate_name' coincides with 'Root_name'
  in the first 'Root_name.size()' letters
  and the remaining letters of 'Gate_name'
  are digits
  
  ====================================*/
bool name_clash(CCUBE &Root_name,Circuit *N,int gate_ind)
{

  Gate &G = N->get_gate(gate_ind);

// special buffer gate does not have a name at this point yet
  if (G.spec_buff_ind >= 0) return(false); 


  CCUBE &Gate_name = G.Gate_name;

  if (Root_name.size() > Gate_name.size()) return(false); 

  for (int i=0; i < Root_name.size(); i++)
    if (Gate_name[i] != Root_name[i]) return(false);

  int count = 0;

  for (int i=Root_name.size(); i < Gate_name.size(); i++) {
    char symb = Gate_name[i];
    if ((symb >= '0') && (symb <= '9')) {
      count++;
      continue;}
    // non-digital symbol
    return(false);
  }
  return(count > 0); // return 'true' if all trailing symbols are digits

} /* end of function name_clash */

/*======================================

  G E N _ S P E C _ B U F F _ N A M E

  =====================================*/
void gen_spec_buff_name(Circuit *N)
{

  CCUBE &Spec_buff_name =  N->Spec_buff_name;

  Spec_buff_name.push_back('z');

  GCUBE &Gate_list = N->Gate_list;

  while (true) {
    bool clash = false;
    for (int i=0; i < Gate_list.size(); i++) {
      if (name_clash(Spec_buff_name,N,i)) {
	clash = true;
	Spec_buff_name.push_back('z'); // add one more letter to the name
	break;
      }
    }
    
    if (clash == false) break;
  }

} /* end of function gen_spec_buff_name */

/*========================================

  S P E C _ B U F F _ G A T E _ I N D

  =======================================*/
int spec_buff_gate_ind(Circuit *N,int ind)
{

  CCUBE fake_name;

  gen_fake_name(fake_name,ind);
  assert(N->Pin_list.find(fake_name) != N->Pin_list.end());

  int gate_ind = N->Pin_list[fake_name];

  Gate &G = N->get_gate(gate_ind);
  assert(G.spec_buff_ind == ind);

  return(gate_ind);

} /* end of function spec_buff_gate_ind */



/*=========================================

  I D E N T I F Y _ C O M M A N D

  =========================================*/
Command_type  identify_command(CCUBE &buf)
{
  int i=0;
  if (compare(buf,".end",i)) return(DOT_END);
  i = 0;
  if (compare(buf,".names",i)) return(DOT_NAMES);
  i = 0;
  if (compare(buf,".latch",i)) return(DOT_LATCH);
  return(WRONG);

} /* end of function identify_command */


/*============================================================

  R E A D _ S T R I N G 
 
  The function returns -1  if eof  occured during reading
  and no symbols has been read into buf

  Otherwise it returns 1.

  The function read in the next line of the file referenced by fp.
  It also reads all the extention lines (if any).
  It then removes from the buf the comment sign "#" and all the
  symbols after it. It also removes the end-of-line symbol ('/n' )

  ==============================================================*/
int read_string(FILE *fp,CCUBE &buf)
{char aux_buf[MAX_LINE];

  buf.clear(); 

  /*----------------------------------------------
    Read the current line and
    all the extension lines
    -------------------------------------------------*/
  while (true) {
    int extension = 0;
    if (fgets(aux_buf,MAX_LINE,fp) == NULL)
      return(-1);
    if (aux_buf[strlen(aux_buf)-2] == '\\') // extension line?
      extension = 1;      
  
    int size = strlen(aux_buf);
    if (size == MAX_LINE-1) { // line is too long?
      printf("increase the value of MAX_LINE\n");
      exit(1);
    }

    for (int i=0; i < size;i++) {
      char symb = aux_buf[i];       
      if ((symb == '#') ||  (symb == '\n'))
	break; 
      if ((symb == '\\') && (extension > 0)) break;
      buf.push_back(aux_buf[i]);
    }   

    if (!extension)
      break;
  }

  return(1);     

} /* end of function read_string */



/*====================================

      R E A D E R _ S T A T E

  ==================================*/
reader_state::reader_state(void)
{
  ignore_missing_end = true;
  add_buffers = true;
  unfinished_gate = false;
  check_fanout_free_inputs = false;
  ignore_errors = false;
} /* end of function read_state */

