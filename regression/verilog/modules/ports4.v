module submodule(input [7:0] data);

  always assert p0: data == 123;

endmodule

module main#(parameter MY_PARAMETER = 123)();

  submodule instance(MY_PARAMETER);

  always assert p1: MY_PARAMETER == 123;

endmodule
