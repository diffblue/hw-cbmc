module div_16(input clk, input [16-1:0] a, b, output reg [16-1:0] q);
  always @(posedge clk) q <= a / b;
endmodule
