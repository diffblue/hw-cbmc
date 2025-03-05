module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // should fail
  initial p0: assert property (x == 0 and x == 1);

  // Given two sequences, 'and' yields a sequence, not a property
  initial p1: assert property (strong(x == 0 and x == 1));

  // But given a property on either side, 'and' yields a property
  initial p2: assert property (x == 0 and nexttime x == 1);
  initial p3: assert property (nexttime x == 1 and x == 0);

  // It also yields a sequence when in parentheses.
  initial p4: assert property ((x == 0 and x != 10) |=> x == 1);

endmodule
