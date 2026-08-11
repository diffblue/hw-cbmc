module pipe_mult(input clk, input [15:0] a, b, output reg [31:0] result);
  reg [15:0] a_r, b_r;
  reg [31:0] mult_r;
  always @(posedge clk) begin
    a_r <= a;
    b_r <= b;
    mult_r <= a_r * b_r;
    result <= mult_r;
  end
endmodule
