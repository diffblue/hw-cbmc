module main;

  logic [7:0] v = 8'hFF;

  // 1800-2017 11.5.1: when the selected range of an indexed part-select
  // falls partly or wholly outside the vector bounds, the out-of-range
  // bits read as x (4-state); this is not an error.
  //
  // v[7 +: 2] selects bits 7 (in range, = 1) and 8 (out of range, = x),
  // so the 2-bit result is not 2'b11.  The property should be PROVED.
  p0: assert final (v[7 +: 2] !== 2'b11);

endmodule
