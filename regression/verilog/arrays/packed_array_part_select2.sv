module main(input clk);

  // Read side of the packed-array part-select bug. A non-indexed
  // part-select on a *packed* array selects a range of ELEMENTS, not
  // bits (1800-2017 7.4.5/7.4.6, 11.5.1). For reg [1:0][7:0] a, the
  // expression a[1:0] denotes elements 1 down to 0, i.e. the full
  // 16-bit value a == 16'hABCD.
  //
  // ebmc instead treats the packed array as a flat vector: the type
  // checker (verilog_typecheck_exprt::convert_trinary_expr, the
  // ID_verilog_non_indexed_part_select case in
  // src/verilog/verilog_typecheck_expr.cpp) calls require_vector(src)
  // and types a[1:0] as a 2-bit vector, so only 2 bits are read into y.
  //
  // Expected (once fixed): y <= a[1:0] copies all 16 bits, so the
  // property holds.

  reg [1:0][7:0] a = 16'hABCD;
  reg [15:0] y;

  always @(posedge clk) y <= a[1:0];

  p0: assert property (@(posedge clk) ##1 y == 16'hABCD);

endmodule
