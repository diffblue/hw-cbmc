// Assigning the result of $clog2 (a mathematical/unbounded integer) to a
// sized localparam requires a concrete width for the integer type in the
// assignment context; the integer type is treated as 32-bit wide
// (IEEE 1800-2017 6.11, 11.8.1).
// Regression for LogikBench blocks/dma (rtl/dma_read.v) and koios/dnnweaver.
module main #(parameter DW = 32)
  (
   input  [DW-1:0] a,
   output [2:0]    out
   );

  localparam [2:0] ARSIZE = $clog2(DW/8);

  assign out = ARSIZE;

endmodule
