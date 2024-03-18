module main;

  wire integer x = 'hff;

  p0: assert property (x[7] == 1);

endmodule
