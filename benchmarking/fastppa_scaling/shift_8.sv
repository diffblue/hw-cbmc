module shift_8(input clk, input [8-1:0] a, input [3-1:0] sh, output reg [8-1:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
