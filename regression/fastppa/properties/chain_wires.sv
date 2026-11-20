module main(input clk, input [31:0] a, b, c, d, output reg [31:0] q);
  wire [31:0] t1 = a + b;
  wire [31:0] t2 = t1 + c;
  always @(posedge clk) q <= t2 + d;
endmodule
