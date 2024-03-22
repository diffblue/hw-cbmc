module main(input i);

  reg some_reg;

  assign some_reg = i;

  // should pass
  always assert p1: some_reg == i;

endmodule
