// Two registers sharing a genuine wire (one adder, two consumers).
// Should count only 1 adder, not 2.
module genuine_sharing(input clk, input [31:0] a, b,
                       output reg [31:0] r1, r2);
  wire [31:0] sum = a + b;
  always @(posedge clk) begin
    r1 <= sum;
    r2 <= sum + 32'd1;
  end
endmodule
