module main;

  // 1800-2017 6.19: x/z requires a four-valued base type
  enum bit [1:0] { A = 0, B = 2'bxx, C = 1 } my_enum;

endmodule
