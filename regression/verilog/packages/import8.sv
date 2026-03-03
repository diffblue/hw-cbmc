package my_pkg;
  parameter my_parameter = 1;
endpackage

module main;
  // This makes my_pkg::my_parameter "potentially locally visible"
  import my_pkg::*;

  // This makes it "locally visible".
  parameter Q = my_parameter;

  // This is an error. The above made my_parameter visible in this scope.
  parameter my_parameter = 2;

endmodule
