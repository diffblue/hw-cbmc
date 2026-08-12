package delays;

  parameter N = 1;

endpackage

module main(input clk);

  parameter N = 1;

  reg [3:0] x = 0;

  always_ff @(posedge clk)
    x++;

  // Per 1800-2017 A.2.10, the delay of ## is a constant_primary (A.8.4),
  // which includes a parenthesized constant expression and a
  // package-scoped parameter identifier.
  p0: assert property (@(posedge clk) x == 0 |-> ##(N + 1) x == 2);
  p1: assert property (@(posedge clk) x == 0 |-> ##(2 * N) x == 2);
  p2: assert property (@(posedge clk) x == 0 |-> ##delays::N x == 1);

endmodule
