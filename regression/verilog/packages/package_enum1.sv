package moo;

  typedef enum { RED, GREEN } my_type;

endpackage

module main;

  assert final (moo::GREEN == 1);

endmodule
