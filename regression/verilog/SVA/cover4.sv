module main;

  // expected to pass
  p0: cover property (1);

  // expected to fail
  p1: cover property (0);

endmodule
