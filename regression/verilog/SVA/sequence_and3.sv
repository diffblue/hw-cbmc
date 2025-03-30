module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // Each LHS match is combined with each RHS match, and hence
  // the below fails owing to the match in the initial time frame.
  initial p1: assert property ((1 or ##2 1) and 1 |-> x == 2);

  // Likewise
  initial p2: assert property (1 and (1 or ##2 1) |-> x == 2);

  // This passes.
  initial p3: assert property ((1 or ##2 1) and 1 |-> (x == 0 || x == 2));

  initial p4: assert property (1 and (1 or ##2 1) |-> (x == 0 || x == 2));

endmodule
