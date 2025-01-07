module main(input clk, input x);

  a0: assume property (not s_eventually !x);

  p0: assert property (x);

endmodule
