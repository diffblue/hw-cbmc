module main;

  genvar i, j, k;

  // 1800-2017 27.6: nested generate loops yield nested arrays of generate
  // blocks, named outer[0].inner[0], outer[0].inner[1], and so on.
  generate
    for(i = 0; i < 2; i = i + 1) begin : outer
      for(j = 0; j < 2; j = j + 1) begin : inner
        wire [7:0] x = 8'd10 + i * 2 + j;
      end
    end
  endgenerate

  initial p0: assert (outer[0].inner[0].x == 8'd10);
  initial p1: assert (outer[0].inner[1].x == 8'd11);
  initial p2: assert (outer[1].inner[0].x == 8'd12);

  // the index can be any elaboration-time constant, including a genvar
  generate
    for(k = 0; k < 2; k = k + 1) begin : chk
      initial p: assert (outer[k].inner[0].x == 8'd10 + k * 2);
    end
  endgenerate

endmodule
