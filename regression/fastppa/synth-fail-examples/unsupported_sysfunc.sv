// Category: unsupported system function
// Error: "unknown system function `$value$plusargs'"
// Cause: Simulation-only system tasks used in synthesizable context
// (common in Chisel-generated Verilog for plusarg_reader).
// Fix: stub out or ignore $value$plusargs in synthesis mode.

module plusarg_example(output reg [31:0] value);
  initial begin
    if (!$value$plusargs("param=%d", value))
      value = 32'd42;
  end
endmodule
