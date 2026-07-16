/* unwinding bound */

void next_timeframe();
extern const unsigned int bound;

/*
  Module verilog::top
*/

struct top_module
{
  unsigned long counter;
};

extern struct top_module top;

int main()
{
  unsigned cycle;
  unsigned val;

  for(cycle = 0; cycle < bound; cycle++)
  {
    val = top.counter;
    assert(val != 5);
    next_timeframe();
  }
}
