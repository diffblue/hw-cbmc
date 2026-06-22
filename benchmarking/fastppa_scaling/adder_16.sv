module adder_16(input clk, input [16-1:0] a, b, output reg [16-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule
