module sub #(parameter N = 32, localparam type T = bit[N-1:0])();

  var T my_var;

endmodule

module main;

  sub #(8) submodule();

  p1: assert final ($bits(submodule.my_var) == 8);

endmodule // main
