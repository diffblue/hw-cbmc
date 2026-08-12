module main;

  // Per 1800-2017 27.4, a genvar that is declared separately from the loop
  // generate construct is not local to any loop, and hence may be shared by
  // two loops in the same scope.

  wire [15:0] some_wire1, some_wire2;

  genvar gi;

  for (gi = 0; gi < 2; gi = gi + 1)
  begin : b1
    wire [7:0] w = gi;
    assign some_wire1[gi*8 +: 8] = w;
  end

  for (gi = 0; gi < 2; gi = gi + 1)
  begin : b2
    wire [7:0] w = gi + 10;
    assign some_wire2[gi*8 +: 8] = w;
  end

  always assert p1: some_wire1 == 16'h0100;

  always assert p2: some_wire2 == 16'h0b0a;

endmodule
