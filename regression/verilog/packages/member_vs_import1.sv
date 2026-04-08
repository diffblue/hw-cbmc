package moo;

  typedef byte some_name;

endpackage

module main;

  import moo::*;

  typedef struct packed {
    // This should not trigger the import,
    // but this doesn't parse with Icarus Verilog.
    int some_name;
  } s;

  // 'some_name' should still be a typedef
  some_name something;

endmodule
