module main(input clk);

  reg [31:0] x;

  initial x=0;

  // 0, 1, ...
  always @(posedge clk)
    x<=x+1;

  // expected to fail: the rhs is evaluated in time frame 0
  initial p0: assert property (1[*0] |=> x==1);

  // expected to pass: the rhs is evaluated in time frame 0
  initial p1: assert property (1[*0] |=> x==0);

  // expected to pass: the lhs is an empty match, and the implication
  // passes vacuously
  initial p2: assert property (1[*0] |-> 0);

endmodule
