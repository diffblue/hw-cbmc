module main;

  // Two loops in the same scope, whose bodies are not surrounded by
  // begin-end, both declare a genvar with the name gi in their header,
  // 1800-2017 27.4.

  wire [1:0] some_wire1, some_wire2;

  for (genvar gi = 0; gi < 2; gi++)
    assign some_wire1[gi] = gi == 1;

  for (genvar gi = 0; gi < 2; gi++)
    assign some_wire2[gi] = gi == 0;

  always assert p1: some_wire1 == 2'b10;
  always assert p2: some_wire2 == 2'b01;

endmodule
