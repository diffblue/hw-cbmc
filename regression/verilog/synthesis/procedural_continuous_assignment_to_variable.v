module main(input i);

  reg some_reg;

  // procedural continuous assignment
  always @i begin
    assign some_reg = i;
  end

  // should pass
  always assert p1: some_reg == i;

endmodule
