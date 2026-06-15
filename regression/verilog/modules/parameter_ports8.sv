module sub #(parameter untyped_port = 1)();

  // If the expression is real, the parameter is real.
  initial assert(untyped_port == 1.5);

endmodule

module main;

  sub #(1.5) submodule();

endmodule // main
