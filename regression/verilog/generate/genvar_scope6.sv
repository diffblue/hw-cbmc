module main;

  // The genvar declared in the loop header shadows both the localparam and
  // the genvar declared in the scope that encloses the loop, 1800-2017 27.4.

  localparam gi = 8'hff;

  wire [15:0] some_wire1, some_wire2;

  if (1)
  begin : outer1
    for (genvar gi = 0; gi < 2; gi++)
    begin : inner
      assign some_wire1[gi*8 +: 8] = gi;
    end
  end

  genvar gj;

  if (1)
  begin : outer2
    for (genvar gj = 0; gj < 2; gj++)
    begin : inner
      assign some_wire2[gj*8 +: 8] = gj + 10;
    end
  end

  always assert p1: some_wire1 == 16'h0100;

  always assert p2: some_wire2 == 16'h0b0a;

endmodule
