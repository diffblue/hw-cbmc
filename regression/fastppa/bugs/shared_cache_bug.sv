// Two independent registers computing the same expression shape.
// Both should be costed - area should be 2x a single adder + registers.
// Bug: structural cache deduplicates them, costing only 1 adder.
module shared_cache_bug(input clk, input [31:0] a, b,
                        output reg [31:0] r1, r2);
  always @(posedge clk) begin
    r1 <= a + b;  // adder 1
    r2 <= a + b;  // adder 2 - same expression, but independent hardware!
  end
endmodule
