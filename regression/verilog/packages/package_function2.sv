package moo;

  function [31:0] foo;
    foo = 123;
  endfunction

endpackage

module main;

  // functions from packages can be elaboration-time constant
  parameter P = moo::foo();

  assert final (P == 123);

endmodule
