/* unwinding bound */

void next_timeframe();
extern const unsigned int bound;

/*
  Module verilog::top
*/

struct top_module
{
  unsigned array[10];
};

extern struct top_module top;

int main()
{
  int i;
  
  for(i=0; i<10; i++)
    assert(top.array[i]==i);
}
