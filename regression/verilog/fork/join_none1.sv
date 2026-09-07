module main;

  parameter int W = 7;

  // Unnamed parallel block terminated by join_none (IEEE 1800-2017 9.3.2).
  // The unnamed form parses to ID_fork, which is not yet supported beyond
  // parsing; it behaves exactly like an unnamed fork ... join.
  initial fork
    p0: assert (W == 7);
  join_none

endmodule
