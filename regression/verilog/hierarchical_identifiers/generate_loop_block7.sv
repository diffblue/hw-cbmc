// The index of a block of a generate loop in a hierarchical reference is
// an elaboration-time constant, which may be an expression over a genvar.
module main;

  for(genvar i = 0; i < 2; i++) begin : blk
    wire [7:0] x = 8'd10 + i;
  end

  for(genvar j = 1; j <= 2; j++) begin : chk
    p0: assert final (blk[j - 1].x == 8'd9 + j);
  end

endmodule
