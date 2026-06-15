module main;

  // A parameter with range but no type is unsiged
  parameter [10:0] P = 8'shff;

  initial assert($bits(P) == 11);
  initial assert(P == 2047);

endmodule
