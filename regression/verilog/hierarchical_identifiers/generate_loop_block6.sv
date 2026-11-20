module main;

  genvar i;

  wire [1:0] blk;

  // 1800-2017 3.13: the name of a generate block is in the module name
  // space, together with the nets and variables of the module.
  generate
    for(i = 0; i < 2; i = i + 1) begin : blk
      wire [7:0] x = 8'd10 + i;
    end
  endgenerate

endmodule
