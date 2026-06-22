module mult_32(input clk, input [32-1:0] a, b, output reg [63:0] p);
  always @(posedge clk) p <= a * b;
endmodule
