module shift_64(input clk, input [64-1:0] a, input [6-1:0] sh, output reg [64-1:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
