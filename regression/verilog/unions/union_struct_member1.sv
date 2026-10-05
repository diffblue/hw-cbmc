// Non-blocking assignment to a member of a packed STRUCT that is nested
// inside a packed UNION.
//
// Per IEEE 1800-2017 7.2.1, the first member of a packed struct occupies
// the most-significant bits, and all members of a packed union overlay the
// same bits.  Here the struct "h" has fields hi (MS 4 bits) and lo (LS 4
// bits), overlaying the 8-bit vector "w".  After writing h.hi = 4'hA and
// h.lo = 4'h5, reading w must yield 8'hA5.
//
// EBMC currently refutes this: verilog_rtl_buildert::decompose_lhs
// (src/verilog/verilog_rtl.cpp) returns {} for the aggregate-typed member
// u.h, so assign_to falls back to lower_lhs, which rewrites the assignment
// into a "with"/member_designator expression on the packed union.  These
// "with" expressions are not lowered to the 1800-2017 7.2.1 bit layout by
// verilog_lowering.cpp (it has no ID_with case), so the solver applies
// CBMC's own LSB-first struct/union flattening and hi/lo end up swapped;
// the trace shows w == 8'h50 instead of 8'hA5.
module main(input clk);

  typedef union packed {
    logic [7:0] w;
    struct packed { logic [3:0] hi, lo; } h;
  } u_t;

  u_t u;

  always @(posedge clk) begin
    u.h.hi <= 4'hA;
    u.h.lo <= 4'h5;
  end

  p0: assert property (@(posedge clk) ##1 u.w == 8'hA5);

endmodule
