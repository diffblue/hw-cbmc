module main(input clk);

  // A non-indexed part-select on a *packed* array selects a range of
  // ELEMENTS, not bits. Per 1800-2017 7.4.5/7.4.6 (and 11.5.1), for
  // reg [1:0][7:0] a the slice a[1:0] denotes elements 1 down to 0, i.e.
  // the full 16-bit value.
  //
  // ebmc instead treats the packed array as a flat vector: the type
  // checker (verilog_typecheck_exprt::convert_trinary_expr, the
  // ID_verilog_non_indexed_part_select case in
  // src/verilog/verilog_typecheck_expr.cpp) calls require_vector(src)
  // and types a[1:0] as unsignedbv{1-0+1} = 2 bits. The RTL builder
  // (verilog_rtl_buildert::decompose_lhs in src/verilog/verilog_rtl.cpp)
  // then writes only a 2-bit slice (--show-rtl shows
  // "main.a[1:0] register, next-state value: 2'b01"), so the 16-bit
  // assignment below does not reach elements a[1] and a[0] correctly.
  //
  // Expected (once fixed): a[1:0] <= 16'hABCD writes a[1] = 8'hAB and
  // a[0] = 8'hCD, so both properties hold.

  reg [1:0][7:0] a = 0;

  always @(posedge clk) a[1:0] <= 16'hABCD;

  p0: assert property (@(posedge clk) ##1 a[1] == 8'hAB);
  p1: assert property (@(posedge clk) ##1 a[0] == 8'hCD);

endmodule
