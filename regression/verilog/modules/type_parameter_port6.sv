module sub #(parameter type T /* no default */)();

  var T my_var;

endmodule

module main;

  // We forgot to assign T, which is an error.
  sub submodule();

endmodule // main
