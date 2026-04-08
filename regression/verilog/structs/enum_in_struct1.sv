module main;

  typedef struct packed {
    // which scope do A, B, C go into?
    enum { A, B, C } some_field;
  } my_type;

  my_type s;

  // This works with Icarus Verilog 12, Riviera Pro 2025.04,
  // Questa 2025.2, Xcelium 25.03, but is rejected by VCS 2025.06.
  initial s.some_field = A;

endmodule
