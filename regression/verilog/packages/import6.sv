package my_pkg;
  parameter my_parameter = 1;
endpackage

module main;
  import my_pkg::my_parameter;

  // this is an error: the identifier is already in the scope
  parameter my_parameter = 2;

endmodule
