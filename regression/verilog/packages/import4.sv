package my_pkg;
  parameter my_parameter = 1;
endpackage

module main;
  parameter my_parameter = 2;
  import my_pkg::*;
  assert final(my_parameter == 2);
endmodule
