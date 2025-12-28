typedef int some_name;

module main;

  wire a, b, c;

  // The identifier 'some_name' can be re-used in the module scope.
  // This works with VCS 2023.03, Questa 2024.3, Xcelium 23.09,
  // Riviera Pro 2023.04, but fails with Icarus Verilog 12.
  and some_name(a, b, c);

endmodule
