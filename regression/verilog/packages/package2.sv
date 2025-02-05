package moo;

  parameter P = 123;

endpackage

module main;

  parameter Q = moo::P;

  assert final (Q == 123);

endmodule
