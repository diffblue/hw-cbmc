parameter some_parameter = 1;
parameter [3:0] other_parameter = 2;
parameter int third_parameter = 3;
parameter dependent_parameter = third_parameter;

module main;
  parameter X = dependent_parameter;
endmodule
