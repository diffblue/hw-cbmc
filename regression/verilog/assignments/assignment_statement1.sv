module main;

  wire [31:0] x, y;

  assign x = 1, y = 2;

  assert final (x == 1 && y == 2);

endmodule
