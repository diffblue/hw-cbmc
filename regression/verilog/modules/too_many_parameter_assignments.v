module my_module#(COUNT = 128)();

endmodule

module main;

  // there is only one parameter port, but two values are given
  my_module #(1, 2) m();

endmodule
