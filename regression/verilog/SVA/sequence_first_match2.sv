module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // Starting from a particular state,
  // first_match yields the sequence that _ends_ first.

  // fails
  initial p0: assert property ((##1 1) or (##2 1) |-> x==1);

  // passes
  initial p1: assert property (first_match((##1 1) or (##2 1)) |-> x==1);

  // fails
  initial p2: assert property (1 or ##1 1 |-> x==0);

  // passes
  initial p3: assert property (first_match(1 or ##1 1) |-> x==0);

endmodule
