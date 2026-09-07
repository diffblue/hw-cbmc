module main;

  parameter int W = 7;

  // Named parallel block terminated by join_none (IEEE 1800-2017 9.3.2).
  // The named form is represented as ID_block, like a named join.
  initial fork : fb
    p0: assert (W == 7);
  join_none

endmodule
