module main;

  // 1800-2017 6.20.2: a parameter without a type takes the type of its
  // value. This parameter is real, and its value is a real constant,
  // not the floating-point encoding used by the back-ends.
  parameter P = 1.5;

  initial assert(P == 1.5);
  initial assert(P > 1);
  initial assert($typename(P) == "real");

  // the same for values given by real expressions
  parameter Q = 1 ? P : 2.5;
  parameter R = P + 1.0;

  initial assert(Q == 1.5);
  initial assert($typename(Q) == "real");
  initial assert(R == 2.5);
  initial assert($typename(R) == "real");

endmodule
