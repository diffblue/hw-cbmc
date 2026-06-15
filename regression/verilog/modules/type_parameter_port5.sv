module sub #(parameter type T /* no default */)();

  var T my_var;

endmodule

module main;

  sub #(byte) submodule();

  p1: assert final ($bits(submodule.my_var) == 8);

endmodule // main
