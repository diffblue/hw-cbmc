module main(input clk, input in);

  // The RHS of the addition will be zero-extended
  initial p1: assert property (8'b1 + 2'sb11 == 8'b100);

endmodule
