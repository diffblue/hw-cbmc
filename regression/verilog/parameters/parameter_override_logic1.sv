module main;

  // A one-bit logic parameter is passed on to a module instance.
  // The value of the parameter is a Boolean constant internally,
  // which must not be mistaken for a literal.
  parameter logic P = 1'b1;
  parameter logic [3:0] Q = 4'b1010;
  parameter logic [3:0] X = 4'b10x1;

  sub #(P, Q, X) s();

endmodule

module sub #(parameter p = 0, q = 0, x = 0);
  initial assert(p == 1);
  initial assert(q == 10);
  initial assert($bits(p) == 1);
  initial assert($bits(q) == 4);
  initial assert($bits(x) == 4);
  initial assert(x === 4'b10x1);
endmodule
