module main(input clk, input [31:0] a, b, c, d, output reg [31:0] q);
  always @(posedge clk) q <= (a + b) + (c + d);
endmodule
