module mult_16(input clk, input [16-1:0] a, b, output reg [31:0] p);
  always @(posedge clk) p <= a * b;
endmodule
