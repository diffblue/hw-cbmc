// hw-cbmc harness_unpack.c fp_adder.v fp_adder.c --module unpack

typedef unsigned __CPROVER_bitvector[6] _u6;
typedef signed __CPROVER_bitvector[10] _s10;
typedef unsigned __CPROVER_bitvector[24] _u24;
typedef unsigned char _u8;
typedef unsigned int _u32;

struct module_unpack {
  _u32 f;
  _Bool uf_nan;
  _Bool uf_inf;
  _Bool uf_zero;
  _Bool uf_subnormal;
  _Bool uf_sign;
  _s10 uf_exponent;
  _u24 uf_significand;
};

extern struct module_unpack unpack;

void set_inputs(void);

typedef struct _bitpattern {
  unsigned int nan:1;
  unsigned int inf:1;
  unsigned int zero:1;
  unsigned int subnormal:1;

  unsigned int sign:1;
  int exponent:10;              // Bias removed
  unsigned int significand:24;  // Leading 1 added
} unpackedFloat;

unpackedFloat unpack_f (float f);

int main()
{
  float f;
  
  // sync the inputs
  unpack.f=*(unsigned *)&f;
  set_inputs();
  
  unpackedFloat result=unpack_f(f);
  
  // check the output
  assert(unpack.uf_sign==result.sign);
  assert(unpack.uf_exponent==result.exponent);
  assert(unpack.uf_significand==result.significand);
  assert(unpack.uf_nan==result.nan);
  assert(unpack.uf_inf==result.inf);
  assert(unpack.uf_zero==result.zero);
  assert(unpack.uf_subnormal==result.subnormal);
  assert(unpack.uf_nan==result.nan);
}
