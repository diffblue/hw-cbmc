module shift_128(input clk, input [128-1:0] a, input [7-1:0] sh, output reg [128-1:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
