module main(input clk, input x);

  // not supported by k-induction
  a0: assume property (not s_eventually !x);

  p0: assert property (x);

endmodule
