module mod_8(input clk, input [8-1:0] a, b, output reg [8-1:0] r);
  always @(posedge clk) r <= a % b;
endmodule
