module main(input clk);

  reg [3:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;

  // A combinational loop through two nets that has no consistent value
  // in the state with cnt == 5: a == !a.
  wire a, b;
  assign a = (cnt == 5) & !b;
  assign b = a;

  // fails in the state with cnt == 3
  p0: assert property (@(posedge clk) cnt != 3);

endmodule
