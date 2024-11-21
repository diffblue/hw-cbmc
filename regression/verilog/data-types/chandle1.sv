module main;

  // IEEE 1800-2017 6.14
  chandle some_handle = null;

  p0: assert final (some_handle == null);
  p1: assert final ($typename(some_handle) == "chandle");

endmodule
