module main(input clock, reset);

  // this uses the default below, and hence passes
  p0: assert property (reset);

  // this does not use the default below, and hence fails
  p1: assert property (disable iff(0) reset);

  default clocking cb @(posedge clk);
  endclocking
  default disable iff (!reset);

endmodule
