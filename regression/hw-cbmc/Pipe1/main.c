/* unwinding bound */

extern const unsigned int bound;

/*
  Module verilog::main
*/

struct module_top
{
  _Bool full0;
  _Bool full2;
};

extern struct module_top top;

void next_timeframe();

int main()
{
  _Bool full0_0=top.full0;
  assert(!top.full2);

  next_timeframe();
  assert(!top.full2);
  
  next_timeframe();
  assert(top.full2==full0_0);
}
