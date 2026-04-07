package my_pkg;
  int x;
endpackage

module main;
  import my_pkg::*;

  task my_task;
    bit x;
    // should pass, it's not my_pkg::x
    assert($bits(x) == 1);
  endtask

  initial my_task();

endmodule
