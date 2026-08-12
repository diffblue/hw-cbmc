module main;

  genvar i;

  // 1800-2017 27.6: a generate loop with a block name yields an array of
  // generate blocks, and the individual blocks are named blk[0], blk[1],
  // and so on.  These names are part of the hierarchy, and hence can be
  // used in hierarchical references.
  generate
    for(i = 0; i < 2; i = i + 1) begin : blk
      wire [7:0] x = 8'd10 + i;
    end
  endgenerate

  initial p0: assert (blk[0].x == 8'd10);
  initial p1: assert (blk[1].x == 8'd11);

endmodule
