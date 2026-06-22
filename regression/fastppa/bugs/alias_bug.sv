module alias_bug(input clk, input [31:0] a, b, output reg [31:0] sum);
  wire [31:0] w1, w2;
  assign w1 = a + b;
  assign w2 = w1;
  always @(posedge clk) sum <= w2;
endmodule
