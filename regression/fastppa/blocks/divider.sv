module divider(input clk, input [31:0] a, b, output reg [31:0] q, r);
  always @(posedge clk) begin
    q <= a / b;
    r <= a % b;
  end
endmodule
