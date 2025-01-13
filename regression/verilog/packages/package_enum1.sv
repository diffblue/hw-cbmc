package moo;

  typedef enum { RED, GREEN } my_type;

endpackage

module main;

  import moo::*;

  assert final (moo::GREEN == 1);

endmodule
