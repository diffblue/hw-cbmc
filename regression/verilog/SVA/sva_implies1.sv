module main;

  // should pass
  p0: assert property (10 implies 20);

  // should fail
  p1: assert property (10 implies 0);

  // should fail
  p2: assert property (10 implies 'bx);

endmodule
