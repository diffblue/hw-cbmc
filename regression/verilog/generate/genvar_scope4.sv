module main;

  // Per 1800-2017 27.4, the genvar declared in the loop header is local to
  // the loop, and hence is not visible after the loop.

  for (genvar gi = 0; gi < 2; gi++)
  begin : b1
    wire w = 0;
  end

  localparam p = gi;

endmodule
