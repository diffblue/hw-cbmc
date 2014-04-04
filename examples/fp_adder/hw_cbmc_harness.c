struct module_fp_add_sub {
  _Bool isAdd;
  unsigned roundingMode;
  unsigned f;
  unsigned g;
  unsigned result;
};

extern struct module_fp_add_sub fp_add_sub;

void set_inputs(void);

float add(int roundingMode, float f, float g);
int compareFloat (float f, float g);

int main()
{
  float f, g;
  float C_result, Verilog_result;
  
  // sync the inputs
  fp_add_sub.f=*(unsigned *)&f;
  fp_add_sub.g=*(unsigned *)&g;
  fp_add_sub.isAdd=1;
  fp_add_sub.roundingMode=0;
  
  set_inputs();
  Verilog_result=*(float *)&fp_add_sub.result;
  
  C_result=add(0, f, g);
  
  // check the output
  assert(compareFloat(C_result, Verilog_result));
}
