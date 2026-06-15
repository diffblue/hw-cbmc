module main;

  // P gets the type of the value, but unsigned
  parameter unsigned P = 8'shff;

  initial assert($bits(P) == 8);
  initial assert(P == 255);

endmodule
