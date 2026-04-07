package my_pkg;
  int some_name;
endpackage

module main;
  import my_pkg::*;

  function [1:0] some_name;
    // should pass, it's not my_pkg::x
    assert($bits(some_name) == 2);
    some_name = 1;
  endfunction

  initial assert(some_name() == 1);

endmodule
