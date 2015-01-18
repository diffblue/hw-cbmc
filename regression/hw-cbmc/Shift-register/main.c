#include <stdio.h>
#define TRUE 1
#define FALSE 0

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/



/*
  Module Verilog::top
*/

struct module_top {
  _Bool Din;
  _Bool En;
  _Bool CLK;
  _Bool Dout;
  _Bool Dout_next;
};

/*
  Hierarchy Instantiation
*/

extern struct module_top top;

struct state_elements_ff_en{
 _Bool Dout;
 _Bool Dout_next;
};
struct state_elements_ff_en sff_en;

void ff_en(_Bool Din, _Bool En, _Bool CLK, _Bool *Dout)
{ 
  _Bool tmp0;
 
 // Sequential block	
 tmp0 = sff_en.Dout_next;
 sff_en.Dout = tmp0;
 
 // Combinational block	
 if(En)
   sff_en.Dout_next = Din;
 else
   sff_en.Dout_next = sff_en.Dout;
}

void main()
{
	_Bool clk;
	_Bool Dout;
  top.En = 0;
	top.Din = 0;
	top.Dout_next = 0;
	set_inputs();
  next_timeframe();
	
	top.En = 1;
	top.Din = 0;
	set_inputs();
  next_timeframe();
  assert(top.Dout == 0);

	top.En = 1;
	top.Din = 1;
	set_inputs();
  next_timeframe();
  assert(top.Dout == 1);
	
	top.En = 1;
	top.Din = 1;
	set_inputs();
  next_timeframe();
  assert(top.Dout == 1);

  top.En = 1;
	top.Din = 0;
	set_inputs();
  next_timeframe();
  assert(top.Dout == 0);

  top.En = 1;
	top.Din = 1;
	set_inputs();
  next_timeframe();
  assert(top.Dout == 1);
}
