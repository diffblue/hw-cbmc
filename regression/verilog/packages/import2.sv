package my_pkg;
  parameter my_parameter = 1;
endpackage

module main;
  import my_pkg::my_parameter;
  assert final(my_parameter == 1);
endmodule
