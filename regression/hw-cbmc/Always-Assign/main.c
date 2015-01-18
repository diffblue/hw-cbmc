/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/



/*
  Module Verilog::up_counter
*/

struct module_top {
  _Bool a;
  _Bool clk;
  _Bool b;
  _Bool d;
  _Bool c;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

struct state_elements_top {
 unsigned int b;
 unsigned int d;
};
struct state_elements_top u1;

unsigned int c;
void top1(unsigned int clk, unsigned int a)
{
  u1.b=a;
  u1.d=c;

  c=u1.b;
}

//void up_counter1(unsigned int clk, unsigned int a);

void main()
{
  top.a=1;
  set_inputs();
  next_timeframe();
  top1(1,1);
  assert(top.b==1);
  assert(u1.b==1);
  assert(u1.b==top.b);
  assert(u1.d==top.d);
  
  top.a=0;
  set_inputs();
  next_timeframe();
  top1(1,0);
  assert(u1.b==top.b);
  assert(u1.d==top.d);
}

