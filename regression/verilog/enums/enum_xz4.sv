module main;

  // 1800-2017 6.19: x/z requires a four-valued base type,
  // also when the base type is given by a typedef
  typedef bit [1:0] two_valued_t;
  enum two_valued_t { A = 0, B = 2'bx0 } my_enum;

endmodule
