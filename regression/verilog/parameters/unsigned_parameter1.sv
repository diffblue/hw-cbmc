module main;

  // P gets the type of the value, but unsigned
  parameter unsigned P = 8'shff;

  initial assert($bits(P) == 8);
  initial assert(P == 255);

  // If the value is an enum, we get the underlying type, but unsigned.
  // Riviera Pro 2025.04 and VCS 2025.06 agree.
  // Xcelium 25.03, Questa 2025.2 return the (signed) underlying type.
  enum bit signed [7:0] { FOO, BAR } some_enum;
  parameter unsigned Q = FOO;
  initial assert ($typename(Q) == "bit[7:0]");

endmodule
