module main;

  int x, y;

  initial begin
    // Assignment pattern on LHS.
    // Does not parse with Icarus Verilog, VCS, XCelium.
    // Works with Riviera, Questa.
    '{x, y} = '{1, 2};

    assert(x == 1 && y == 2);
  end

endmodule
