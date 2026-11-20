module multiplier(input clk, input [15:0] a, b, output reg [31:0] p);
  always @(posedge clk) p <= a * b;
endmodule
