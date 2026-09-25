module main(input clk);

  reg [3:0] c = 0;

  always @(posedge clk)
    c <= c + 1;

  // The operand of s_eventually is itself a temporal property.
  // c is never 20, hence "always c != 20" holds in every state.
  // Expected to pass.
  p0: assert property (s_eventually always c != 20);

endmodule
