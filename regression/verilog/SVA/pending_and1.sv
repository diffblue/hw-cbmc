// Pending match propagation through the SVA 'and' sequence operator.
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // ack[->2] and ack[->3] have no concrete matches (different end times).
  // Both produce pending matches; the 'and' operator must propagate pending.
  // BUG: pending flag is lost in sva_and -- the cross product uses max(end_time),
  //      producing a non-pending match that ##0 then spuriously evaluates.
  a1: assert property (
      @(posedge clk) req |=> (ack[->2] and ack[->3]) ##0 (val == 1)
  );

endmodule
