module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // should pass
  initial p0: assert property (x == 0 or x == 1);

  // Given two sequences, 'or' yields a sequence, not a property
  initial p1: assert property (strong(x == 0 or x == 1));

  // But given a property on either side, 'or' yields a property
  initial p2: assert property (x==0 or nexttime x == 1);
  initial p3: assert property (nexttime x==1 or x == 1);

  // It also yields a sequence when in parentheses.
  initial p4: assert property ((x == 0 or x != 10) |=> x == 1);

endmodule
