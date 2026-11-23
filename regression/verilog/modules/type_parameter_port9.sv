module leaf #(parameter type T = int)(input T i, output T o);
  assign o = i;
endmodule

module mid #(parameter type T = int)(input T i, output T o);
  // ordered override, passing on the type parameter of mid
  leaf #(T) l(.i(i), .o(o));
endmodule

module main;

  typedef logic [7:0] byte_t;

  typedef struct packed {
    logic [3:0] a;
    logic [3:0] b;
  } pair_t;

  byte_t i, o;
  pair_t pi, po;

  // typedefs of the instantiating module, named and ordered
  mid #(.T(byte_t)) m1(.i(i), .o(o));
  mid #(pair_t) m2(.i(pi), .o(po));

  always_comb assert (o == i);
  always_comb assert (po == pi);
  always_comb assert ($bits(m1.l.i) == 8);

endmodule
