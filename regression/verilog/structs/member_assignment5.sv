module main(input clk, input [3:0] in);

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } s_t;

  s_t s;

  // Combinational: only hi is assigned, so s becomes a wire.
  // lo is unconstrained (nondeterministic); only hi is checked.
  always @* s.hi = in;

  p0: assert property (@(posedge clk) s.hi == in);

endmodule
