/* unwinding bound */

extern const unsigned int bound;


/*
  Module verilog::sub1
*/

struct module_sub1 {
  unsigned int   a;
  unsigned int   z;
};

/*
  Module verilog::top
*/

struct module_top {
  unsigned int   variable;
  struct module_sub1 s;
  _Bool          clk;
};

extern struct module_top top;

void next_timeframe();

int main()
{
  unsigned cycle;

  for(cycle=0; cycle<bound; cycle++)
  {
    assert(top.variable==top.s.z);
    next_timeframe();
  }
}
