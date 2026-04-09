package moo;
  typedef struct packed {
    int some_name; // should not end up in the scope
  } some_type;
endpackage

typedef byte some_name;

module main;

  import moo::*;

  // 'some_name' should still be a typedef
  some_name something;

endmodule
