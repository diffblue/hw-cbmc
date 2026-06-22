module shared_comparator_bug(input clk, input [31:0] a, b,
                            output reg lt, eq, gt);
  always @(posedge clk) begin
    lt <= (a < b);
    eq <= (a == b);
    gt <= (a > b);
  end
endmodule
