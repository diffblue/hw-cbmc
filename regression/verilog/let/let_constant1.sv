module main;

  let some_let = 8'd123;

  // The standard doesn't say, but we allow these to be elaboration-time
  // constants.
  // This is errored by VCS 2025.06, but allowed by
  // Questa 2025.2, Xcelium 25.03, Riviera Pro 2025.04.
  parameter some_parameter = some_let;

  initial assert(some_parameter == 123 && $bits(some_parameter) == 8);

endmodule
