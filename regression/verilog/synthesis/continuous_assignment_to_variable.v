module main(input i);

  reg some_reg;

  // should error
  assign some_reg = i;

endmodule
