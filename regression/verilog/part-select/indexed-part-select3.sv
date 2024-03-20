module main(input [7:0] in, input [2:0] where);

  // The base index of an indexed part-select
  // does not need to be constant.
  wire out = in[where +: 1];

  p0: assert property (out == in[where]);

endmodule
