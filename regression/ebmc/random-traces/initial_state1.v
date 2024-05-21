module m(input clk);

  // x is unconstrained
  reg [31:0] x;
  always @(posedge clk) x = x + 1;

  // y is constrained
  reg [31:0] y;
  always @(posedge clk) y = y + 1;
  initial y = 123;

endmodule
