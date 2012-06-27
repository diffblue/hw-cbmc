/* unwinding bound */

extern const unsigned int bound;

/*
  Module verilog::main
*/

struct module_top
{
  unsigned variable;
  _Bool   in;
};

extern struct module_top top;

void next_timeframe();
void set_inputs();

_Bool nondet_bool();

int main()
{
  unsigned cycle;
  unsigned i;
  
  i=0;

  for(cycle=0; cycle<bound; cycle++)
  {
    assert(i==top.variable);
    _Bool increment=nondet_bool();
    top.in=increment;
    if(increment) i++;
    set_inputs();
    next_timeframe();
  }
}
