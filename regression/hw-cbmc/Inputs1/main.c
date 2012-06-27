/* unwinding bound */

void next_timeframe();
void set_inputs();
extern const unsigned int bound;

/*
  Module verilog::top
*/

struct top_module
{
  unsigned long variable;
  _Bool enable;
};

extern struct top_module top;

int main()
{
  _Bool e_in;

  assert(top.variable==0);

  top.enable=e_in;
  set_inputs();
  next_timeframe();

  assert(top.variable==(e_in?1:0));
}
