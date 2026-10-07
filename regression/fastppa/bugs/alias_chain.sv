// Chain of wire aliases: sum -> alias1 -> alias2
// Two registers use different aliases of the same underlying computation.
// Should count the adder only once (both paths lead to same wire).
module alias_chain(input clk, input [31:0] a, b,
                   output reg [31:0] r1, r2);
  wire [31:0] sum = a + b;
  wire [31:0] alias1 = sum;
  wire [31:0] alias2 = sum;
  always @(posedge clk) begin
    r1 <= alias1;
    r2 <= alias2 + 32'd1;
  end
endmodule
