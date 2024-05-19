module main(input i);

  reg some_reg;

  // continuous assignment to variables are not allowed in Verilog
  assign some_reg = i;

endmodule
