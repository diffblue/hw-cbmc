// Pending match propagation through the SVA 'throughout' sequence operator.
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // ack[->2] can produce a pending match (ack fires fewer than 2 times).
  // '1 throughout ack[->2]' adds a trivially-true LHS condition and passes
  // through the match, but must propagate the pending status.
  // BUG: sva_sequence_throughout creates a concrete result from a pending
  //      sequence match, so ##0 then spuriously evaluates val.
  a1: assert property (
      @(posedge clk) req |=> (1 throughout ack[->2]) ##0 (val == 1)
  );

endmodule
