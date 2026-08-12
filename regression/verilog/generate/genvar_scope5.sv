module main;

  // Per 1800-2017 27.4, the genvar declared in the loop header is local to
  // the loop, and hence shadows the wire with the same name in the scope
  // that encloses the loop.

  wire [7:0] gi = 8'hff;
  wire [15:0] some_wire;

  if (1)
  begin : outer
    for (genvar gi = 0; gi < 2; gi++)
    begin : inner
      assign some_wire[gi*8 +: 8] = gi;
    end
  end

  always assert p1: some_wire == 16'h0100;

endmodule
