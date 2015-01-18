#define TRUE 1
#define FALSE 0
#include <assert.h>
#include <stdio.h>

// ********* HW-CBMC interface **********//
/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[2] _u2;



/*
  Module Verilog::and1
*/

struct module_and1 {
  _u4 a;
  _u4 b;
  _u4 c;
  _u4 d;
  _u4 c_0;
};

/*
  Module Verilog::top
*/

struct module_top {
  _u4 in1;
  _u4 in2;
  _u4 o1;
  _u4 o2;
  _u2 x;
  _u2 y;
  struct module_and1 A1;
  struct module_and1 A2;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ********** Implementation in C ***********//
struct state_elements_and1{
  unsigned char c;
};
unsigned char andc(unsigned char a, unsigned char b, unsigned char *c, unsigned char *d)
{
  struct state_elements_and1 sand1;
  sand1.c = a & b & 15;
  *c = a & b & 15; // New 
  *d = 1; // Support pointer type assignment in continuous statements
  return;
}

struct state_elements_top {
  struct state_elements_and1 A1;
  struct state_elements_and1 A2;
};
struct state_elements_top stop;

void top1(unsigned int in1, unsigned int in2)
{
  unsigned char o1, o2;
	unsigned char x=0;
	unsigned char y=1;
  andc(in1, in2, &stop.A1.c, &o2);
  andc(stop.A1.c, in2, &stop.A2.c, &o2);
}

void main()
{
  top.in1=1;
  top.in2=1;
  set_inputs();
  top1(1,1);
  assert(top.A1.c==stop.A1.c);
  assert(top.A2.c==stop.A2.c);
 
  top.in1=7;
  top.in2=3;
  set_inputs();
  top1(7,3);
  assert(top.A1.c==stop.A1.c);
  assert(top.A2.c==stop.A2.c);

  top.in1=5;
  top.in2=10;
  set_inputs();
  top1(5,10);
  assert(top.A1.c==stop.A1.c);
  assert(top.A2.c==stop.A2.c);
}


