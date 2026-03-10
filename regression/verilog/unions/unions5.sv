module minimal(input clk, input [15:0] in);

  typedef struct packed { logic [15:0] data; } wrap_t;
  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } split_t;

  typedef union packed {
    split_t s;
    wrap_t  w;
  } u_t;

  wire u_t x = in;

  a0: assume property (@(posedge clk) in[3:0] == 4'h0);

  // All three check the same bits: x[3:0] == 0
  p0: assert property (@(posedge clk) x.w.data[3:0] == 4'h0);
  p1: assert property (@(posedge clk) x.s.lo[3:0] == 4'h0);
  p2: assert property (@(posedge clk) x[3:0] == 4'h0);

endmodule
