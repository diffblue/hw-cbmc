module main(input clk);

  bit a = 1, b = 0;

  always_ff @(posedge clk) begin
    a = !a;
    b = !b;
  end

  // a b a b ...
  initial assert property ((a ##1 b)[*5]);

  // !b !a !b !a ...
  initial assert property ((!b ##1 !a)[*5]);

endmodule
