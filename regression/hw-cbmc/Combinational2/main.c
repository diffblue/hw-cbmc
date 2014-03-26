void set_inputs(void);

/*
  Module verilog::top
*/

struct top_module
{
  unsigned int in, out;
  unsigned int shift;
};

extern struct top_module top;

int main()
{
  top.in=20;
  set_inputs();
  assert(top.out==(20<<16));
  assert(top.shift==16);
}
