module main;

  // Two unnamed loops in the same scope may both declare a genvar with the
  // name gi in their header, 1800-2017 27.4. The blocks of the loops are
  // named genblk1[0], genblk1[1] and genblk2[0], genblk2[1], 1800-2017 27.6.

  wire [15:0] some_wire1, some_wire2;

  for (genvar gi = 0; gi < 2; gi++)
  begin
    wire [7:0] w = gi;
    assign some_wire1[gi*8 +: 8] = w;
  end

  for (genvar gi = 0; gi < 2; gi++)
  begin
    wire [7:0] w = gi + 10;
    assign some_wire2[gi*8 +: 8] = w;
  end

  always assert p1: some_wire1 == 16'h0100;
  always assert p2: some_wire2 == 16'h0b0a;
  always assert p3: genblk1[1].w == 1 && genblk2[1].w == 11;

endmodule
