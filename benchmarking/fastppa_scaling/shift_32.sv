module shift_32(input clk, input [32-1:0] a, input [5-1:0] sh, output reg [32-1:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
