module main;

  // Per 1800-2017 27.4, a genvar declared in the loop_generate_construct
  // header is local to that loop.  Two loops in the same scope may hence
  // both use the name gi.

  wire [15:0] some_wire1, some_wire2;

  for (genvar gi = 0; gi < 2; gi++)
  begin : b1
    wire [7:0] w = gi;
    assign some_wire1[gi*8 +: 8] = w;
  end

  for (genvar gi = 0; gi < 2; gi++)
  begin : b2
    wire [7:0] w = gi + 10;
    assign some_wire2[gi*8 +: 8] = w;
  end

  // main.b1[0].w is 0 and main.b1[1].w is 1
  always assert p1: some_wire1 == 16'h0100;

  // main.b2[0].w is 10 and main.b2[1].w is 11
  always assert p2: some_wire2 == 16'h0b0a;

endmodule
