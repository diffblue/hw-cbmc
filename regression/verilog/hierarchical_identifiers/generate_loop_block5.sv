module main;

  genvar i;

  generate
    for(i = 0; i < 2; i = i + 1) begin : blk
      wire [7:0] x = 8'd10 + i;
    end
  endgenerate

  // there is no block blk[2]
  initial p0: assert (blk[2].x == 8'd12);

endmodule
