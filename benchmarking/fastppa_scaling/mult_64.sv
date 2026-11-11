module mult_64(input clk, input [64-1:0] a, b, output reg [127:0] p);
  always @(posedge clk) p <= a * b;
endmodule
