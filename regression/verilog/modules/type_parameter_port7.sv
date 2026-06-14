module sub #(parameter type T = int)();

  var T my_var;

endmodule

module main;

  // T is a type, not a value, which is an error.
  sub #(123) submodule();

endmodule // main
