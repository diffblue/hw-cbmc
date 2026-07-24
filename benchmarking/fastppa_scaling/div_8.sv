module div_8(input clk, input [8-1:0] a, b, output reg [8-1:0] q);
  always @(posedge clk) q <= a / b;
endmodule
