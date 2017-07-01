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
#include "dnf_io.hh"
const int factor = 1000;

/*================================================

    P R I N T _ N U M _ W I T H _ C O M M A S

  ================================================*/
void print_num_with_commas(const int &num)
{

  CUBE parts;
  int Num = num;
  while (true) {
     int remainder = Num % factor;
      int quotient = Num / factor;
      parts.push_back(remainder);
      if (quotient == 0) break;
      Num = quotient;
    }

  size_t num_of_parts=parts.size();
  for (size_t i=0; i < num_of_parts; i++) {
    if (i ==  0) std::cout << parts[num_of_parts-i-1];
    else std::cout << parts[num_of_parts-i-1];
     
    if (i != num_of_parts-1) std::cout << ",";
  }
} /* end of function print_num_with_commas */

/*=====================================================


  M Y _ P R I N T F

  This function is my version of printf
  that prints integer numbers separting thousands
  with commas

  =====================================================*/
void my_printf(const char *format,...)
{

  va_list ap;

  va_start(ap,format); // n is the last parameter before the '...' 
                       // in the function header
  while (*format) {
    int c = *format++;
    if (c != '%') {
      std::cout << (char) c; 
      continue;
    }
    int spec = *format++;
    assert(spec == 'm');
    int num = va_arg(ap,int);
    print_num_with_commas(num);      
  }
  va_end(ap);

} /* end of function my_printf */
