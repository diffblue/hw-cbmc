module adder_8(input clk, input [8-1:0] a, b, output reg [8-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
