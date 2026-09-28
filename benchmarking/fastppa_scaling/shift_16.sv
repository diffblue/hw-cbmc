module shift_16(input clk, input [16-1:0] a, input [4-1:0] sh, output reg [16-1:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
