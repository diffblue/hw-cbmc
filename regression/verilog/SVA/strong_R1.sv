// Test for incorrect encoding of strong release (strong_R / s_until_with).
//
// "a s_until_with b" maps to strong_R(b, a), which should mean:
// F(b) ∧ (b R a), i.e., b eventually holds, and a holds at every step
// up to and including the step when b first holds.
//
// The bug in property.cpp encodes strong_R(p, q) as F(q) ∧ (p W q)
// instead of the correct F(p) ∧ (p R q).
//
// p0: The lhs of s_until_with never holds (counter never exceeds 14
//     since it saturates at 10), so the property should be REFUTED by
//     the strong eventuality requirement.

module main(input clk);

  reg [3:0] counter = 0;

  always_ff @(posedge clk)
    if(counter < 10)
      counter <= counter + 1;

  // "1 s_until_with (counter > 14)" should be REFUTED:
  // counter never exceeds 10, so the strong requirement that the lhs
  // (counter > 14) eventually holds is not met.
  initial p0: assert property (1 s_until_with (counter > 4'd14));

endmodule
