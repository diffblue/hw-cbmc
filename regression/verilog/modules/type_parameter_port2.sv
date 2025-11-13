module sub #(parameter type T = int)();

  var T my_var;

endmodule

module main;

  sub #(.T(byte)) submodule();

  p1: assert final ($bits(submodule.my_var) == 8);

endmodule // main
