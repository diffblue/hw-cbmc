module main(input clk, input i);

  reg r;

  initial r = 1;

  always @(posedge clk) r <= i;

  // A counterexample would need r in every state, and !r two or
  // three states later. Hence, the property holds.
  initial p0: assert property (s_eventually (r |-> always [2:3] r));

endmodule
