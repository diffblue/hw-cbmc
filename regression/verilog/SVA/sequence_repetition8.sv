module main(input clk);

  // Distinguish [->n] (goto repetition) from [=n] (non-consecutive repetition).
  //
  // [->1] ends at the first cycle where b is true.
  // [=1] can end at any cycle at or after the first b,
  //       provided b does not occur again, i.e., it allows
  //       trailing cycles where b is false.
  //
  // x:    0 1 2 3 4 ...
  // b:    0 1 0 0 0 ...   (true only at cycle 1)
  // c:    1 1 1 0 0 ...   (true at cycles 0-2, false from cycle 3)
  //
  // b[->1] |=> c  should PASS: endpoint is cycle 1, checks c at cycle 2 (true)
  // b[=1]  |=> c  should FAIL: endpoint can be cycle 1, 2, 3, ...
  //                             at endpoint cycle 3, checks c at cycle 4 (false)

  reg [7:0] x = 0;

  always_ff @(posedge clk)
    x <= x + 8'd1;

  wire b = (x == 8'd1);
  wire c = (x <= 8'd2);

  // should pass
  initial p0: assert property (b[->1] |=> c);

  // should fail
  initial p1: assert property (b[=1] |=> c);

endmodule
