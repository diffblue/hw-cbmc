module main;

  typedef enum { A, B } e_t;
  e_t e;

  // 1800-2017 11.5.1: vector range bounds may be negative.  The type
  // of v is printed in the error message and must show the declared
  // range [7:-8], not a wrapped-around unsigned value.
  logic [7:-8] v;

  always_comb e = v;

endmodule
