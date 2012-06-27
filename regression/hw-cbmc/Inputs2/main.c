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
  unsigned long in_var;
};

extern struct top_module top;

int main()
{
  // tf 0
  assert(top.variable==0);
  top.in_var=10;
  set_inputs();
  next_timeframe();
  
  // tf 1
  assert(top.variable==10);
  top.in_var+=10; // now 20
  set_inputs();
  next_timeframe();
  
  // tf 2
  assert(top.variable==20);
  top.in_var=10; // now 10
  set_inputs();
  next_timeframe();
  
  // tf 3
  assert(top.variable==10);
  top.in_var+=30; // now 40
  set_inputs();
  next_timeframe();
  
  // tf4
  assert(top.variable==100); // fails, it's 40
}
