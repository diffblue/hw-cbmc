typedef int some_identifier;

module main;
  // This does _not_ parse with Icarus Verilog version 12.0, but does parse
  // with Riviera Pro 2025.04, Xcelium 25.03, Questa 2025.2 and VCS 2025.06.
  wire some_identifier;
  assign some_identifier = 1;
endmodule
