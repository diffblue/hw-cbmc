module main(input clk);

  parameter CYCLES = 2;
  localparam DELAY = CYCLES + 1;

  reg [3:0] x = 0;

  always_ff @(posedge clk)
    x++;

  // Per 1800-2017 A.2.10, cycle_delay_range is
  //   ## constant_primary | ## [ cycle_delay_const_range_expression ] | ...
  // and a constant_primary (A.8.4) covers a parameter identifier as well as
  // a parenthesized constant expression.  The delay in ##n therefore need
  // not be a literal number.
  p0: assert property (@(posedge clk) x == 0 |-> ##CYCLES x == CYCLES);
  p1: assert property (@(posedge clk) x == 0 |-> ##(CYCLES) x == CYCLES);
  p2: assert property (@(posedge clk) x == 0 |-> ##DELAY x == DELAY);

endmodule
