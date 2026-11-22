module sub(input a, input b, input c, output o);

  assign o = a ^ b;

endmodule

module main;

  wire a = 1, b = 1, x = 0;
  wire o;

  // .* connects a (and o) by name. b is connected explicitly and
  // is not affected by the wildcard. c has no counterpart in main
  // and remains unconnected.
  sub m(.*, .b(x));

  always_comb assert (o == 1);

endmodule
