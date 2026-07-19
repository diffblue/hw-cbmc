module main;

  initial assert($typename(real)=="real");
  initial assert($typename(shortreal)=="shortreal");
  initial assert($typename(realtime)=="realtime");

endmodule
