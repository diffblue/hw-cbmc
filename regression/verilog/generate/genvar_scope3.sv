module main;

  // The genvar declared in the loop header is in the same scope as the
  // wire, and hence this is a conflict.

  wire gi;

  for (genvar gi = 0; gi < 2; gi++)
  begin : b1
    wire w = 0;
  end

endmodule
