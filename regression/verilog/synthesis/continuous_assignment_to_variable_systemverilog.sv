module main(input i);

  reg some_reg;

  // continuous assignments to variables are allowed in SystemVerilog
  assign some_reg = i;

  // should pass
  p1: assert final (some_reg == i);

endmodule
