// Pending match propagation through the SVA 'intersect' sequence operator.
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // ack[->2] intersect ack[->3]: pending matches of both sides have the same
  // end_time (they are both at the bound), so 'intersect' does combine them.
  // The result must be a pending match, not a concrete match at the bound.
  // BUG: pending flag lost in sva_sequence_intersect -- produces a non-pending
  //      match that ##0 then spuriously evaluates.
  a1: assert property (
      @(posedge clk) req |=> (ack[->2] intersect ack[->3]) ##0 (val == 1)
  );

endmodule
