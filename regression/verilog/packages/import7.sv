package my_pkg;
  parameter my_parameter = 1;
endpackage

module main;
  import my_pkg::*;

  // this is ok: my_pkg::P is only "potentially locally visible" (1800 2017 26.3)
  parameter my_parameter = 2;

endmodule
