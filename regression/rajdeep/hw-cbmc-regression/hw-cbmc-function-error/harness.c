extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);

// type declarations
typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[64] _u64;

// Module Verilog::main

struct module_vmain {
  _u4 in;
  _u4 out;
  _u4 result;
};
// top module
extern struct module_vmain vmain;

int main()
{
  vmain.in = 1;
  set_inputs();
  next_timeframe();

  assert(vmain.result == 1);
}
