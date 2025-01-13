package moo;

  parameter P = 123;

endpackage

module main;

  import moo::*;

  parameter Q = moo::P;

  assert final (Q == 123);

endmodule
