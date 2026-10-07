module main(input clk, input [7:0] in1, input [7:0] in2);

  // a -> b -> c is the cone of the properties
  reg [7:0] a, b, c;
  wire [7:0] w;

  // big1 -> big2 -> big3 is unrelated to the properties
  reg [31:0] big1, big2, big3;

  assign w = in1 + 1;

  initial begin
    a = 0; b = 0; c = 0;
    big1 = 0; big2 = 0; big3 = 0;
  end

  always @(posedge clk) begin
    a <= w;
    b <= a;
    c <= b;
    big1 <= big1 * in2 + 3;
    big2 <= big2 ^ big1;
    big3 <= big3 + big2;
  end

  p0: assert property (c == 0 || c != 0);
  p1: assert property (c != 8'd42);

endmodule
