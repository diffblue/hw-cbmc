package moo;

  typedef byte my_type;

endpackage

module main;

  import moo::*;

  moo::my_type some_var;

  assert final ($typename(some_var) == "byte");

endmodule
