// Pending match propagation through first_match().
// https://github.com/diffblue/hw-cbmc/issues/1763

module m(input logic clk, req, ack);
  logic val;
  assign val = ack;

  // first_match(ack[->1]): when ack never fires, ack[->1] has only a pending
  // match at the bound.  first_match should propagate it as pending.
  // BUG: the pending match at the bound wins the 'earliest end_time' search
  //      because its stored end_time (no_timeframes-1) is used directly;
  //      first_match returns it as a concrete match and ##0 spuriously
  //      evaluates val.
  a1: assert property (
      @(posedge clk) req |=> first_match(ack[->1]) ##0 (val == 1)
  );

endmodule
