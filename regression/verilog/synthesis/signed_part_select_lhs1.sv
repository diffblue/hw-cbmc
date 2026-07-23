// Minimal reproducer for a synthesis crash triggered by the LogikBench
// arithmetic/mulreg benchmark.
//
// A full-width part-select on the left-hand side of a *signed* register
// used to abort synthesis with a type-consistency invariant violation.
// A part-select expression is unsigned even when it selects the entire
// vector (IEEE 1800-2017 11.5.1), and the shortcut for full-width
// part-selects assigned the (unsigned) right-hand side straight into the
// signed register, so the left- and right-hand sides differed in
// signedness.  A non-constant right-hand side is required, as constants
// are folded to the matching type before the check.
module main(input clk, input signed [15:0] a);

  // assigned via a full-width part-select (the construct under test)
  reg signed [15:0] via_part_select = 0;

  // assigned directly, for reference
  reg signed [15:0] via_whole = 0;

  always @(posedge clk)
    begin
      via_part_select[15:0] <= a;
      via_whole <= a;
    end

  // the full-width part-select assignment preserves the (signed) value
  p0: assert property (via_part_select == via_whole);

endmodule
