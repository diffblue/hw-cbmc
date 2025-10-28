module main;

  typedef struct packed {int a, b;} S;
  S my_s;
  int x, y;

  initial begin
    // Assignment pattern on LHS.
    // Does not parse with Icarus Verilog, VCS, XCelium.
    // Works with Riviera, Questa.
    '{x, y} = S'{1, 2};

    assert(x == 1 && y == 2);
  end

endmodule
