module my_module(input [31:0] x, y, z = 5);

endmodule

module main();

  my_module m1(.x(1), .y(), .z());

  // 1800-2017 23.3.3.2 says
  // "If left unconnected, the port shall have the default
  // initial value corresponding to the data type."
  // This is 'x for logic types.
  // However, Icarus Verilog, VCS, Questa, Xcelium use 'z.

  initial assert (m1.x == 1);
  initial assert (m1.y === 'z);
  initial assert (m1.z == 5);

  my_module m2(/* blank */, 1, /* blank */);

  initial assert (m2.x === 'z);
  initial assert (m2.y == 1);
  initial assert (m2.z == 5);

endmodule
