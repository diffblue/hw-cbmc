// Pending match propagation through ##n when RHS of the delay generates a pending match.
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // (1'b1 ##1 ack[->1]) can produce a pending match (ack never fires).
  // ##0 must propagate the pending as vacuous, not evaluate val at time 0.
  // BUG: the pending flag is lost through the inner ##1 RHS,
  //      so ##0 then evaluates val at an earlier timeframe -- spurious failure.
  a1: assert property (
      @(posedge clk) req |=> 1'b1 ##1 ack[->1] ##0 (val == 1)
  );

endmodule
