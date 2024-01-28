module main;

  wire [15:0] some_wire;

  generate
    genvar i;
    for (i = 0; i <= 15; i = i + 1) begin
      // a localparam may depend on a genvar
      localparam p = i;
      assign some_wire[p] = (p%2) == 0;
    end
  endgenerate

  // should pass
  always assert property1: some_wire == 'b0101_0101_0101_0101;

endmodule
