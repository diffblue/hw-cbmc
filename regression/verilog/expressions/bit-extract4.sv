module main;

  wire integer x = 'hff;

  p0: assert final (x[7] == 1);

endmodule
