/* unwinding bound */

void next_timeframe();
extern const unsigned int bound;

/*
  Module verilog::top
*/

struct top_module
{
  unsigned long variable;

  // don't confuse with module
  unsigned top;
};

extern struct top_module top;

int main()
{
  unsigned cycle;
  unsigned val;

  for(cycle=0; cycle<bound; cycle++)
  {
    val=top.variable;
    assert(val==cycle);
    next_timeframe();
  }
}
