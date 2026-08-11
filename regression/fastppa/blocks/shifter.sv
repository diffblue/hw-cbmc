module shifter(input clk, input [31:0] a, input [4:0] sh, output reg [31:0] y);
  always @(posedge clk) y <= a << sh;
endmodule
