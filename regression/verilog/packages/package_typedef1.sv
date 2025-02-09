package moo;

  typedef byte my_type;

endpackage

module main;

  moo::my_type some_var;

  assert final ($typename(some_var) == "byte");

endmodule
