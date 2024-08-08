module main;

  module my_module;
    wire [7:0] value = 123;
  endmodule

  my_module m();

  assert final (m.value == 123);

endmodule
