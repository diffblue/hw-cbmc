module main;

  // IEEE 1800-2017 6.14
  chandle some_handle = null;

  assert final (!some_handle);
  assert final ($typename(some_handle) == "chandle");

endmodule
