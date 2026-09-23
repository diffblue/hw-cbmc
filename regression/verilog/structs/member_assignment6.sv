module main(input clk, input sel);

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } s_t;

  s_t s;

  initial s = 8'h05;

  // Member-wise assignment guarded by if/else; lo must hold its value.
  always @(posedge clk)
    if(sel)
      s.hi = 4'hA;
    else
      s.hi = 4'hB;

  p0: assert property (@(posedge clk) s.lo == 4'h5);

endmodule
