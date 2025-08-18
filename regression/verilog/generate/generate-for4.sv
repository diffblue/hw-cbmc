module main;

  wire [15:0] some_wire;

  generate
    genvar i;
    for (i = 0; i <= 15; ++i)
      assign some_wire[i] = (i%2) == 0;
  endgenerate

  // should pass
  always assert property1: some_wire == 'b0101_0101_0101_0101;

endmodule
