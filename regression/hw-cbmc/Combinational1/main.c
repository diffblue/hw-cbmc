void set_inputs();
void next_timeframe();

/*
  Module verilog::top
*/

struct top_module
{
  unsigned int in1, in2;
  unsigned int out;
};

extern struct top_module top;

int main()
{
  top.in1=10;
  top.in2=20;
  set_inputs();
  assert(top.out==30);

  next_timeframe();
  top.in1=11;
  top.in2=21;
  set_inputs();
  assert(top.out==32);
}
