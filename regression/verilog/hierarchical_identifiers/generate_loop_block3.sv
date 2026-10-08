module sub;

  genvar i;

  generate
    for(i = 0; i < 2; i = i + 1) begin : blk
      wire [7:0] x = 8'd10 + i;
    end
  endgenerate

endmodule

module main;

  sub s();

  // 1800-2017 27.6: the generate block names are part of the hierarchy of
  // the module, and hence can be reached through the module instance.
  initial p0: assert (s.blk[0].x == 8'd10);
  initial p1: assert (s.blk[1].x == 8'd11);

endmodule
