module main;

  // should pass
  p0: assert property (10 and 20);

  // should fail
  p1: assert property (10 and 0);

  // should fail
  p2: assert property (10 and 'bx);

endmodule
