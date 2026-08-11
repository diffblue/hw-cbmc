module mod_64(input clk, input [64-1:0] a, b, output reg [64-1:0] r);
  always @(posedge clk) r <= a % b;
endmodule
