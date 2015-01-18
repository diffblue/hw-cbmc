#include <stdio.h>
#define TRUE 1
#define FALSE 0

// ************* hw-cbmc interface *********************
/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned char _u8;


/*
  Module Verilog::up_counter
*/

struct module_up_counter {
  _u8 out;
  _Bool enable;
  _Bool clk;
  _Bool reset;
  _u8 out_0;
};




/*
  Hierarchy Instantiation
*/

extern struct module_up_counter up_counter;

// ************* Implementation in C *******************
struct state_elements_up_counter{
  unsigned char out;
};
struct state_elements_up_counter  sup_counter;

void up_counter1(unsigned char *out, _Bool enable, _Bool clk, _Bool reset)
{
  unsigned char tmp1;
  unsigned char tmp0;
  if(reset)
  {
    tmp0 = 0;
  }

  else
    if(enable)
    {
      tmp1 = (unsigned char)(unsigned int)sup_counter.out + 1;
    }

  if(reset)
  {
    *out = tmp0 & 255;
		sup_counter.out = tmp0 & 255;
  }

  else
    if(enable)
    {
			*out = tmp1 & 255;
      sup_counter.out = tmp1 & 255;
    }
}

int main()
{
  // Inputs of C program
  _Bool enable;
  _Bool clk;
  _Bool reset;
  unsigned char out;
  
	// call to C function
  up_counter1(&out, 0, clk, 1);
  // set Verilog inputs
  up_counter.enable = 0;
  up_counter.reset = 1;
  set_inputs();
  next_timeframe();
  assert(up_counter.out == sup_counter.out);
  
	// Start counting, set enable = 1
  up_counter.reset = 0;
  up_counter.enable = 1;
  set_inputs();
  next_timeframe();
  up_counter1(&out, 1, clk, 0);
  assert(up_counter.out == sup_counter.out);
  
  up_counter.enable = 1;
  set_inputs();
  next_timeframe();
  up_counter1(&out, 1, clk, 0);
  assert(up_counter.out == sup_counter.out);

  up_counter.enable = 1;
  set_inputs();
  next_timeframe();
  up_counter1(&out, 1, clk, 0);
  assert(up_counter.out == sup_counter.out);
  
  up_counter.enable = 1;
  set_inputs();
  next_timeframe();
  up_counter1(&out, 1, clk, 0);
  assert(up_counter.out == sup_counter.out);
}  
 
