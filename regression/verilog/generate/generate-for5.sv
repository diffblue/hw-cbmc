module main;

  wire [15:0] some_wire;

  generate
    genvar i;
    for (i = 16; i != 0; i--)
      assign some_wire[i - 1] = ((i-1)%2) == 0;
  endgenerate

  // should pass
  always assert property1: some_wire == 'b0101_0101_0101_0101;

endmodule
