module main;

  logic [7:0] v = 8'hA5;

  // 1800-2017 11.5.1: in an indexed part-select the width expr2 "shall
  // be a positive constant expression".  Zero is not positive, so a
  // zero-width part-select such as v[3 +: 0] is illegal and must be
  // rejected the same way a negative width is.
  p0: assert final (v[3 +: 0] == 0);

endmodule
