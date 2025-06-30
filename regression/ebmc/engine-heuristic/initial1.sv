module main(input clk, input x);

  a0: assume property (x);

  initial p0: assert property (x);

endmodule
