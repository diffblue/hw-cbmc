module main;

  logic [7:0] v = 8'hA5;

  // 1800-2017 11.5.1: in an indexed part-select "expr1 +: expr2" or
  // "expr1 -: expr2", expr2 (the width) "shall be a positive constant
  // expression".  A negative width is illegal and must be rejected.
  p0: assert final (v[3 +: -1] == 0);

endmodule
