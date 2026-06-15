module main;

  parameter unsigned [10:3] Q = 8'hff;

  initial assert($left(Q) == 10);
  initial assert($right(Q) == 3);

  // P gets the type of the value, but with range [size-1:0]
  parameter P = Q;

  initial assert($bits(P) == 8);
  initial assert($left(P) == 7);
  initial assert($right(P) == 0);

endmodule
