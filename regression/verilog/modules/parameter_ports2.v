module sub #(parameter an_eight_bit_parameter_port = 1)();

  // 1800 2017 6.20.2
  // A parameter declaration with no type or range specification shall
  // default to the type and range of the final value assigned to the
  // parameter,
  always assert p1: $bits(an_eight_bit_parameter_port) == 8;

endmodule

module main;

  sub #(8'd123) submodule();

endmodule // main
