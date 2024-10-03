module main;

  wire [15:0] some_wire;

  // The generate ... endgenerate became optional with 1364-2005.
  genvar i;
  for (i = 0; i <= 15; i = i + 1)
    assign some_wire[i] = (i%2) == 0;

  // should pass
  always assert property1: some_wire == 'b0101_0101_0101_0101;

endmodule
