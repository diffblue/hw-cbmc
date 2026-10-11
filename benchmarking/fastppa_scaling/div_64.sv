module div_64(input clk, input [64-1:0] a, b, output reg [64-1:0] q);
  always @(posedge clk) q <= a / b;
endmodule
