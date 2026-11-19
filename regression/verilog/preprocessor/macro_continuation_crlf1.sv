`define ADD_ONE(x) ((x) + \
  1)
`define ADD_TWO(x) ((x) + // continue \
  2)

module main;
  p0: assert property (`ADD_ONE(3) == 4 && `ADD_TWO(3) == 5);
endmodule
