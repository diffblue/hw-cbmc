module mod_32(input clk, input [32-1:0] a, b, output reg [32-1:0] r);
  always @(posedge clk) r <= a % b;
endmodule
