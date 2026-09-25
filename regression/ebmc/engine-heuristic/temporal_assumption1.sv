module main(input clk, input a, input b);

  reg s = 0;

  always @(posedge clk)
    s <= a | (s & b);

  // The assumption has hidden state (the value of a in the previous
  // cycle), which is not among the state variables of the design.
  assume property (a |=> b);

  // Fails at t=2: a@0=1 forces b@1=1, and thus s@1=1 and s@2=1,
  // but b@2 is unconstrained as a@1=0.
  p0: assert property (s -> b);

endmodule
