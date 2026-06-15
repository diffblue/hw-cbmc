module sub #(parameter int N = 123)();

endmodule

module main;

  // N is a value, not a type, which is an error.
  sub #(int) submodule();

endmodule // main
