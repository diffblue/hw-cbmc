/******************************************************

Module: Auxiliary functions (Part 2)

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <queue>
#include <assert.h>
#include <stdio.h>
#include "dnf_io.hh"
#include "ccircuit.hh"
#include "r0ead_blif.hh"


/*=============================================

           E R R O R _ M E S S A G E

===============================================*/
void error_message(err_type error_name,CCUBE &buf)
{

 switch (error_name)
   {case WRONG_EOF:
         printf("end-of-file occured before the '.end' command\n");
         return;
    case WRONG_SYNTAX:
         printf("WRONG_SYNTAX:\n");
         print_name(&buf); printf("\n");
         return;
   default: assert(false); // shouldn't reach this line
 
   }


}/* end of function error_message */


/*=============================================

           E R R O R _ M E S S A G E

===============================================*/
void error_message(const char *message,CCUBE &buf)
{

  printf("%s\n",message); 
  print_name(&buf); printf("\n");
   


}/* end of function error_message */

/*===============================================================

                  C O M P A R E
 Returns 1 if the substring (0..b.size()-1) of a is equl to b.
 Otherwise, it returns 0. The function also changes the 
 index i. If the function returns 1 index i is equal to b.size()
================================================================*/
int compare(CCUBE &a,std::string const &b,int &i)
{
 for (; i < b.size();i++)
   if (a[i]!=b[i])
     return(0);
 return(1);


}/* end of function compare */

/*=========================================

            S T R _ S I Z E

 The funcion returns the number of 
 symbols in a string. (Its main use it
 to count characters in string constants
=======================================*/
int str_size(std::string const &s)
{
  return(s.size());
}/* end of function str_size */


/*======================================

          C O P Y _ N A M E

======================================*/
void copy_name(CCUBE &buf,CCUBE &name,
               int &i)
{
  for (i; i< buf.size();i++)
    {if ((buf[i] == ' ') || (buf[i] == '\t'))
	break;
      name.push_back(buf[i]);
    }
} /* end of function copy_name */

/*====================================

               B L A N K _ L I N E 

 The function returns 1 if it contains
 only spaces  and tabulation symbols.
 Otherwise it returns 0

=====================================*/
int blank_line(CCUBE &buf)
{
  for (int i=0; i < buf.size();i++)
    if ((buf[i] == ' ') || (buf[i] == '\t'))
      continue;
    else
      return(0);
  return(1);
}/* end of function blank_line */

/*=======================================

  S K I P _ B L A N K S

  The function skips spaces and tabulation
  symbols
  =========================================*/
void skip_blanks(CCUBE &buf,int &i)
{
  for (; i < buf.size();i++)
    if ((buf[i] == ' ') || (buf[i] == '\t'))
      continue;
    else
      break;
}/* end of function skip_blanks */

