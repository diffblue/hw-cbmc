module main;

  // A parameter with range but no type is unsiged
  parameter [10:0] P = 8'shff;

  initial assert($bits(P) == 11);
  initial assert(P == 2047);

  // In case of an enum, we use the underlying type.
  enum bit unsigned [7:0] { FOO, BAR } some_enum;
  parameter [10:0] Q = FOO;
  initial assert ($typename(Q) == "bit[10:0]");

endmodule
