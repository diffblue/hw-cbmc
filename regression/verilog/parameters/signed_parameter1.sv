module main;

  // P gets the type of the value, but signed
  parameter signed P = 8'hff;

  initial assert($bits(P) == 8);
  initial assert(P == -1);

  // If the value is an enum, we get the underlying type, but signed.
  // VCS 2025.06 and Xcelium 25.03 agree.
  // Riviera Pro 2025.04 and Questa 2025.2 return the (unsigned) underlying type.
  enum bit unsigned [7:0] { FOO, BAR } some_enum;
  parameter signed Q = FOO;
  initial assert ($typename(Q) == "bit signed[7:0]");

endmodule
