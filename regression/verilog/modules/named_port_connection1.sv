module my_module(input a, b);

endmodule

module main();

  // a is connected twice
  my_module m1(.a(1), .a(1));

endmodule
