module main(input clk, input x);

  // unsupported
  a0: assume property (not s_eventually !x);

  // should fail
  p0: assert property (0);

endmodule
