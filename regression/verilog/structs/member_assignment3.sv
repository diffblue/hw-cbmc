module main(input clk);

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } s_t;

  s_t s;

  initial s = 8'h05;

  // Only hi is assigned; lo must hold its value.
  always @(posedge clk)
    s.hi = 4'hA;

  p0: assert property (@(posedge clk) s.lo == 4'h5);
  p1: assert property (@(posedge clk) ##1 s == 8'hA5);

endmodule
