typedef int some_identifier;

module main;
  // This does _not_ parse with Icarus Verilog version 12.0, nor with
  // Riviera Pro 2025.04, nor with VCS 2025.06.
  // This does parse with Xcelium 25.03 and Questa 2025.2.
  parameter some_identifier = 123;
  assert final(some_identifier == 123);
endmodule
