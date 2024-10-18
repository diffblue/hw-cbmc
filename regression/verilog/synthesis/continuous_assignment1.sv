module main;

  wire [31:0] a;
  assign a[7:0] = 1;
  assign a[8+:24] = 1;

  assert final (a == 'h101);

endmodule
