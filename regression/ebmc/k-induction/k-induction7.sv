module main(input clk, input x, input y);

  reg z = 0;
  always_ff @(posedge clk) z <= z || x;

  // unsupported assumption
  a0: assume property (not s_eventually !y);

  // supported assumption
  a1: assume property (!x);

  // inductive property
  p0: assert property (!z);

endmodule
