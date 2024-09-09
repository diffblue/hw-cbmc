module main;

  // should pass
  p0: assert property (not 0);

  // should fail
  p1: assert property (not 1);

endmodule
