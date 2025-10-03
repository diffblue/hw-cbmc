module M(input [31:0] some_name);

  initial assert (some_name == 123);

endmodule

module main;

  // typedef with the same name as a port
  typedef bit [31:0] some_name;

  // This fails to parse with Icarus Verilog,
  // but works with VCS, Questa, Xcelium, Riviera
  M my_instance(.some_name(123));

endmodule
