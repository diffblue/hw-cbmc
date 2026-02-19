package moo;

  function [31:0] foo;
    foo = 123;
  endfunction

endpackage

module main;

  assert final (moo::foo() == 123);

endmodule
