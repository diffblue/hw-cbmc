module main(input clk, input rst);

  // counts 0, 1, ..., 10, 0, ...; may be reset to 0 at any time
  reg [3:0] c = 0;

  always_ff @(posedge clk)
    c <= (rst || c == 10) ? 0 : c + 1;

  // concurrent assertions are implicitly 'always'

  // expected to pass: c only leaves 0..9 via 10
  p0: assert property ((c <= 9) until (c == 10 || c == 0));

  // expected to fail: c == 5 is reached before c == 6
  p1: assert property ((c != 5) until (c == 6));

  // expected to pass: every loop visits c == 0
  p2: assert property ((c <= 9) s_until (c == 10 || c == 0));

  // expected to fail: resetting forever never reaches c == 10
  p3: assert property ((c <= 9) s_until (c == 10));

  // expected to pass: c <= 10 is invariant
  p4: assert property ((c <= 10) until_with (c == 10));

  // expected to fail: starting at c == 3
  p5: assert property ((c != 3) until_with (c == 2));

  // expected to pass: c <= 10 is invariant, and every loop visits c == 0
  p6: assert property ((c <= 10) s_until_with (c == 0));

  // expected to fail: resetting forever never reaches c == 10
  p7: assert property ((c <= 10) s_until_with (c == 10));

endmodule
