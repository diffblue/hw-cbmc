module main;

  // 1800-2017 6.20.2: a parameter without a type takes the type of its
  // value. This parameter is real, and keeps its type when used in
  // an expression or passed on to a module instance.
  parameter P = 1.5;

  initial assert(P == 1.5);
  initial assert(P > 1);
  initial assert($typename(P) == "real");

  sub #(P) s();

endmodule

module sub #(parameter p = 0);
  initial assert(p == 1.5);
  initial assert($typename(p) == "real");
endmodule
