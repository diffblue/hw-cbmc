module sub #(parameter byte P = 0);

  initial assert($bits(P) == 8);
  initial assert(P == 2);

endmodule

module main;

  sub #('h102) submodule();

endmodule // main
