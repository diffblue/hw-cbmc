package my_pkg;
  int x;
endpackage

module main;
  import my_pkg::*;

  // ANSI syntax
  task my_task(input x);
    // should pass, it's not my_pkg::x
    assert($bits(x) == 1);
  endtask

  initial my_task(0);

endmodule
