module my_module;
  parameter magic_number = 123;

  wire [15:0] some_wire = magic_number;

endmodule

module top;

  my_module m1(), m2();
  defparam m1.magic_number = 456;  // override
  defparam m2.magic_number = 789;  // override

  initial assert(m1.some_wire == 456);
  initial assert(m2.some_wire == 789);

endmodule
