/* unwinding bound */

extern const unsigned int bound;

/*
  Module verilog::main
*/

struct module_top
{
  __CPROVER_bool var1[101];
  unsigned long  var2;
};

extern struct module_top top;

void next_timeframe();

int main()
{
  unsigned cycle, i, j;

  for(cycle=0; cycle<bound; cycle++)
  {
    i=(top.var2>>3)&1;
    j=top.var1[3];  
    assert(i==j);
    next_timeframe();
  }
}
