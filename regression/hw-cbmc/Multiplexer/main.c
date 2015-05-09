#define TRUE 1
#define FALSE 0

#include <stdio.h>

// ********** hw-cbmc interface **************//
/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);

/*
  Type declarations
*/

typedef unsigned __CPROVER_bitvector[2] _u2;
typedef unsigned __CPROVER_bitvector[4] _u4;

/*
  Module Verilog::top
*/

struct module_top {
  _u2 select;
  _u4 d;
  _Bool q;
};

/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ********** implementation in C ***************//

struct state_elements_mux{
  _Bool q;
};
struct state_elements_mux  smux;

void topc(unsigned char select, unsigned char d, _Bool *q)
{
  int t;
  if((unsigned int)select == 0) {
    smux.q = d & 0x1;
    *q = d & 0x1;
  }
  else
    if((unsigned int)select == 1) {
      smux.q = (d >> 1) & 0x1;
      *q = (d >> 1) & 0x1;
    }
    else
      if((unsigned int)select == 2) {
       smux.q = (d >> 2) & 0x1;
       *q = (d >> 2) & 0x1;
      }
      else
          if((unsigned int)select == 3) {
            smux.q = (d >> 3) & 0x1;
            *q = (d >> 3) & 0x1;
          }
}

void main() {
  unsigned char select;
  unsigned char d;
  _Bool q;
  top.select=0;
  top.d=1;
  set_inputs();
  topc(0, 1, &q);
  assert(top.q == q);
  
  top.select=1;
  top.d=2;
  set_inputs();
  topc(1, 2, &q);
  assert(top.q == q);

  top.select=2;
  top.d=3;
  set_inputs();
  topc(2, 3, &q);
  assert(top.q == q);
}
