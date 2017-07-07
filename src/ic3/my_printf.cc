/******************************************************

Module: Structuring the output of large numbers by
        using commas

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <set>
#include <algorithm>
#include <queue>
#include <map>
#include <iostream>
#include <iomanip>
#include <util/message.h>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"

#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

const int group_factor = 1000;

/*================================================

    P R I N T _ N U M _ W I T H _ C O M M A S

  ================================================*/
void CompInfo::print_num_with_commas(unsigned message_level,const int &num)
{

  messaget::mstreamt &Ms = M->get_mstream(message_level);
  CUBE parts;
  int Num = num;
  while (true) {
     int remainder = Num % group_factor;
      int quotient = Num / group_factor;
      parts.push_back(remainder);
      if (quotient == 0) break;
      Num = quotient;
    }

  size_t num_of_parts=parts.size();
  for (size_t i=0; i < num_of_parts; i++) {
    if (i ==  0) Ms << parts[num_of_parts-i-1];
    else Ms << std::setfill('0') <<  std::setw(3)
		   << parts[num_of_parts-i-1];
     
    if (i != num_of_parts-1) Ms << ",";
  }
} /* end of function print_num_with_commas */

/*=====================================================


  M Y _ P R I N T F

  This function is my version of printf
  that prints integer numbers separting thousands
  with commas

  =====================================================*/
void CompInfo::my_printf(unsigned message_level,const char *format,...)
{

  va_list ap;

  va_start(ap,format); // n is the last parameter before the '...' 
                       // in the function header

  bool flushed = false;
  messaget::mstreamt &Ms = M->get_mstream(message_level);
  while (*format) {
    int c = *format++;
    if (c == '\n') {
      Ms << M->eom;
      flushed = true;
      continue;}
    
    if (c != '%') {
      Ms << (char) c;
      continue;
    }
    int spec = *format++;
    assert(spec == 'm');
    int num = va_arg(ap,int);
    print_num_with_commas(message_level,num);      
  }
  va_end(ap);

  if (!flushed) Ms << M->eom;
} /* end of function my_printf */
