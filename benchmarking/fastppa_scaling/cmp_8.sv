module cmp_8(input clk, input [8-1:0] a, b, output reg lt, eq, gt);
  always @(posedge clk) begin
    lt <= (a < b);
    eq <= (a == b);
    gt <= (a > b);
  end
endmodule
