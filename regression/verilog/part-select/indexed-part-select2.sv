module main(input [7:0] in, input [2:0] width);

  // The width of an indexed part-select must be a constant
  wire [7:0] out = in[0 +: width];

endmodule
