module main;

  // 1800-2017 6.20.2: a parameter without a type takes the type of its
  // value. These parameters are real, and keep their type when passed
  // on to a module instance.
  parameter P = 1.5;
  parameter Q = P + 1.0;

  sub #(P, 1.5) s1();
  sub #(Q, 2.5) s2();

endmodule

module sub #(parameter p = 0, parameter real expected = 0.0);
  initial assert(p == expected);
  initial assert($typename(p) == "real");
endmodule
