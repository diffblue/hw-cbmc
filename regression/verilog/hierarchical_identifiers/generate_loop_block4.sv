module main;

  genvar i;

  generate
    for(i = 0; i < 2; i = i + 1) begin : blk
      wire [7:0] x = 8'd10 + i;
    end
  endgenerate

  // 1800-2017 27.6: the generate blocks are part of the hierarchy of the
  // module, and hence can also be reached from $root.
  initial p0: assert ($root.main.blk[1].x == 8'd11);

endmodule
