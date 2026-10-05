module main(input clk);

  // Write to an unpacked array element with a constant index that is
  // outside the declared range.  Per IEEE 1800-2017 7.4.6, "Writing to
  // an array with an invalid index ... shall perform no operation."
  // The out-of-range write mem[4] must hence be a silent no-op (at most a
  // warning), and the assertion must hold: PROVED, EXIT=0.
  //
  // EBMC instead rejects the write with a hard error
  //   "array index out of range" / CONVERSION ERROR (exit code 2),
  // thrown in verilog_rtl_buildert::decompose_lhs
  // (src/verilog/verilog_rtl.cpp).

  reg [3:0] mem [0:3];

  always @(posedge clk) mem[4] <= 4'd1;

  p0: assert property (@(posedge clk) 1);

endmodule
