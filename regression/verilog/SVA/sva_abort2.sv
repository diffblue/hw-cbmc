module main(input clk);

  reg [7:0] counter = 0;

  always_ff @(posedge clk)
    counter++;

  // 1800-2017 16.12.11: the abort condition is checked at every cycle
  // during the evaluation of the operand property, not only in the
  // first cycle.

  // The operand is evaluated from t=2 to t=7; counter==4 is reached at
  // t=4, during the evaluation, and hence rejects.  Expected to fail.
  p0: assert property (@(posedge clk) counter == 1 |=> reject_on (counter == 4) always[0:5] counter < 100);

  // The operand fails at t=4 (counter==4), but counter==3 at t=3 accepts
  // before that.  Expected to pass.
  p1: assert property (@(posedge clk) counter == 1 |=> accept_on (counter == 3) always[0:5] counter < 4);

endmodule
