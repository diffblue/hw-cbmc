module main(input clk);

  // Test that a sequence match at the bound does not cause the
  // entire non-overlapped implication to become vacuously true.
  //
  // x:    0 1 2 3 4 5
  // c:    1 1 1 0 0 0   (true at cycles 0-2, false from cycle 3)
  //
  // 1[*1:$] matches at every cycle from 0 onwards. With |=>,
  // the consequent c is checked one cycle later. At match cycle 2,
  // c at cycle 3 is false, so the property should fail.
  //
  // The match at the last bound cycle has its consequent beyond
  // the bound; this must not discard earlier obligations.

  reg [7:0] x = 0;

  always_ff @(posedge clk)
    x <= x + 8'd1;

  wire c = (x <= 8'd2);

  // should fail
  initial p0: assert property (1[*1:$] |=> c);

endmodule
