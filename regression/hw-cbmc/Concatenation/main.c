#include <stdio.h>
#define TRUE 1
#define FALSE 0

// ********* hw-cbmc interface *************//

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned char _u8;
typedef unsigned __CPROVER_bitvector[10] _u10;


/*
  Module Verilog::top
*/

struct module_top {
  _u8 y;
  _u8 z;
  _u10 x;
  _u10 x_0;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ************ Implementation in C ********************//

struct state_elements_top{
  unsigned short int x;
};
struct state_elements_top  stop;

void topc(unsigned char y, unsigned char z, unsigned short int *x)
{
  stop.x = (((y >> 2) & 15) << 6) | ((z >> 1) & 0x3F);

  *x = (((y >> 2) & 15) << 6) | ((z >> 1) & 0x3F);
}


void main() {
  unsigned short int x;
	
	top.y=15;
	top.z=20;
	set_inputs();
	topc(15, 20, &x);
	assert(top.x==x);
	
	top.y=10;
	top.z=26;
	set_inputs();
	topc(10, 26, &x);
	assert(top.x==x);
}

