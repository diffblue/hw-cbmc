module main(input clk, input x, input y);

  // constrain both inputs to TRUE
  a0: assume property (x);
  a1: assume property (y);

  reg z = 1;
  always @(posedge clk) z <= x & y;

  // z stays TRUE because both inputs are constrained
  p0: assert property (z);

endmodule
