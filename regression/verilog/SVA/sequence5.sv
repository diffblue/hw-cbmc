module main;

  // passes, since 10 is true
  initial p0: assert property (10);

  // fails, since 0 isn't true
  initial p1: assert property (0);

  // fails, since 'x' isn't true
  initial p2: assert property (1'bx);

  // fails, since 'z' isn't true
  initial p3: assert property (1'bz);

endmodule
