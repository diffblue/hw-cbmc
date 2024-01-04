module sub #(parameter an_eight_bit_parameter_port = 1)();

  always assert p1: $bits(an_eight_bit_parameter_port) == 8;

endmodule

module main;

  sub #(123) submodule();

endmodule // main
