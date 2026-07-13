module main(input clk, input a, input b);

  // s_until_with is the strong form of until_with.
  // "a s_until_with b" means: b holds at every cycle until and including
  // the cycle where a holds, AND a must eventually hold (the strong part).
  //
  // The bug: sva_to_ltl.cpp lowers s_until_with to ordinary R (release),
  // which does NOT enforce the "a must eventually hold" requirement.
  // It should be lowered to strong release.

  // This property should be REFUTED: 0 never holds, so the strong
  // requirement (lhs must eventually become true) is violated.
  // With the buggy lowering to ordinary R, it is incorrectly PROVED
  // because R allows lhs to never hold as long as rhs holds forever.
  p0: assert property (0 s_until_with 1);

endmodule
