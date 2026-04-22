// This goes into $unit
parameter int some_identifier = 123;

// The module goes into the "definitions name space".
// This is rejected by Icarus Verilog 12, Riviera Pro 2025.04,
// but accepted by Xcelium 25.03, Questa 2025.2, VCS 2025.06.
module some_identifier;

  // This resolves to $unit::some_identifier
  initial assert(some_identifier==123);

endmodule
