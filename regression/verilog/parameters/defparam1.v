module my_module;
  parameter magic_number = 123;

  wire [15:0] some_wire = magic_number;

endmodule

module top;

  my_module m1();
  defparam m1.magic_number = 456;  // override

  always assert p1: m1.some_wire == 456;

endmodule
