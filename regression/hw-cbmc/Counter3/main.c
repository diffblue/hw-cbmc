#include <assert.h>

/* unwinding bound */

extern const unsigned int bound;

/*
  Module verilog::main
*/

struct module_top
{
  unsigned long var1;
  unsigned long var2;
};

extern struct module_top top;

void next_timeframe();

int main()
{
  unsigned value;

  next_timeframe();
  next_timeframe();
  next_timeframe();
  next_timeframe();
  next_timeframe();
  value=top.var1;
  next_timeframe();
  assert(value==top.var2);
}
