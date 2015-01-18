#include <stdio.h>
#define TRUE 1
#define FALSE 0

// *********** hw-cbmc Interface ************* //

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/


/*
  Module Verilog::ff
*/

struct module_ff {
  _Bool CLK;
  _Bool Din;
  _Bool Dout;
  _Bool q;
};

/*
  Module Verilog::top
*/

struct module_top {
  _Bool cs;
  _Bool ns;
  _Bool CLK;
  _Bool Din;
  _Bool En;
  _Bool Dout;
  struct module_ff ff1;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

struct state_elements_ff{
  _Bool q;
};

_Bool ffc(_Bool CLK, _Bool Din, _Bool *Dout)
{
  struct state_elements_ff  sff;
  _Bool tmp0;
  tmp0 = Din;
  sff.q = tmp0;
  *Dout = sff.q;
  return;
}

struct state_elements_ff_en{
  _Bool ns;
  struct state_elements_ff ff1;
};
struct state_elements_ff_en  sff_en;

void topc(_Bool CLK, _Bool Din, _Bool En, _Bool *Dout)
{
  _Bool cs;
  if(En)
  {
    sff_en.ns = Din;
  }

  else
  {
    sff_en.ns = cs;
  }
  ffc(CLK, sff_en.ns, &cs);
	*Dout = cs;
  
}

void main()
{ 
  _Bool clk;
	_Bool out;
	top.En = 1;
	top.Din = 0;
	set_inputs();
	next_timeframe();
  topc(clk,0,1,&out);
	assert(top.Dout == out);
	
	top.En = 1;
	top.Din = 1;
	set_inputs();
	next_timeframe();
  topc(clk,1,1,&out);
	assert(top.Dout == out);

	top.En = 1;
	top.Din = 0;
	set_inputs();
	next_timeframe();
  topc(clk,0,1,&out);
	assert(top.Dout == out);

	top.En = 1;
	top.Din = 1;
	set_inputs();
	next_timeframe();
  topc(clk,1,1,&out);
	assert(top.Dout == out);
}

