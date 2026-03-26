// Pending match propagation through the SVA 'within' sequence operator.
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // ack[->2] (RHS of 'within') can produce a pending match.
  // A pending RHS means the containing interval extends beyond the bound;
  // the result of 'within' must also be pending.
  // BUG: sva_sequence_within treats the pending RHS as a concrete match at
  //      the bound, so 'within' creates a non-pending result and ##0 then
  //      spuriously evaluates val.
  a1: assert property (
      @(posedge clk) req |=> ((ack[->1]) within (ack[->2])) ##0 (val == 1)
  );

endmodule
