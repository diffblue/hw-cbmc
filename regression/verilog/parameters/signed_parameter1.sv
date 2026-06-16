module main;

  // P gets the type of the value, but signed
  parameter signed P = 8'hff;

  initial assert($bits(P) == 8);
  initial assert(P == -1);

endmodule
