module div_32(input clk, input [32-1:0] a, b, output reg [32-1:0] q);
  always @(posedge clk) q <= a / b;
endmodule
