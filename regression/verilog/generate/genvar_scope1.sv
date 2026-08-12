module main;

  // Per 1800-2017 27.4, a genvar declared in the loop_generate_construct
  // header is local to that loop.  Two loops in the same scope may hence
  // both use the name gi.

  for (genvar gi = 0; gi < 2; gi++)
  begin : b1
    wire [7:0] w = gi;
  end

  for (genvar gi = 0; gi < 2; gi++)
  begin : b2
    wire [7:0] w = gi + 10;
  end

endmodule
