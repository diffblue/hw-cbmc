module main(input clk, input a, input b);

  // A single time frame does not suffice to observe a match of a ##1 b.
  // The negation of the sequence cannot be refuted within bound 0.
  // Expected to pass up to the bound.
  p0: assert property (@(posedge clk) not strong(a ##1 b));
  p1: assert property (@(posedge clk) not weak(a ##1 b));

endmodule
