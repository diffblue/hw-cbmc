module mult_8(input clk, input [8-1:0] a, b, output reg [15:0] p);
  always @(posedge clk) p <= a * b;
endmodule
