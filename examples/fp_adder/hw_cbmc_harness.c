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
  float C_result, f, g;
  
  // sync the inputs
  fp_add_sub.f=f;
  fp_add_sub.g=g;
  fp_add_sub.isAdd=1;
  fp_add_sub.roundingMode=1;
  
  set_inputs();
  
  C_result=add(0, f, g);
  
  // check the output
  assert(compareFloat(C_result, fp_add_sub.result));
}
