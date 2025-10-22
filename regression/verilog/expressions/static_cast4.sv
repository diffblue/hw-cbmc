module main;

  // The standard suggests that casts can be applied to assignment patterns.
  // VCS, Icarus Verilog and Xcelium error this.
  // Questa allows it.
  // Riviera throws an internal error.

  typedef struct packed { int a, b; } S;

  initial begin
    S some_struct;
    some_struct.a = 1;
    some_struct.b = 2;
    assert ((S'('{a: 1, b: 2})) == some_struct);
  end

endmodule
