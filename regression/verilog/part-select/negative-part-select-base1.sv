module main;

  logic [7:0] v = 8'hFF;

  // 1800-2017 11.5.1: the base (expr1) of an indexed part-select may be
  // any expression, including one that evaluates to a negative value.
  // If part of the selected range is outside the vector bounds, those
  // out-of-range bits read as x (for a 4-state value); this is not an
  // error.
  //
  // Here v[-1 +: 2] selects bits -1 and 0: bit -1 is out of range (reads
  // x), bit 0 is in range (1), so the 2-bit result is not 2'b11.
  p0: assert final (v[-1 +: 2] !== 2'b11);

endmodule
