module main;

  wire [31:0] array[10];

  assign array[0] = 0;
  assign array[1] = 1;

  assert final (array[0] == 0);
  assert final (array[1] == 1);

endmodule
