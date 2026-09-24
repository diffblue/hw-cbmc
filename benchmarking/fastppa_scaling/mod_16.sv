module mod_16(input clk, input [16-1:0] a, b, output reg [16-1:0] r);
  always @(posedge clk) r <= a % b;
endmodule
