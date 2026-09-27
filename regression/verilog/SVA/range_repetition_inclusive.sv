// Test for SVA inclusive range repetition [*n:m]
// This tests the fix for the CRITICAL soundness bug where [*n:m] was
// incorrectly using exclusive upper bound, causing the m-repetition match
// to be omitted.

module main(input clk, req, c);

  // Property with inclusive range [*2:3]
  // Should generate obligations for BOTH 2 and 3 repetitions
  // Before fix: only generated length-2 match
  // After fix: generates both length-2 and length-3 matches
  p: assert property (@(posedge clk) req[*2:3] |-> c);

endmodule
