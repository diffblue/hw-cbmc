module main(input clk);

  typedef union packed {
    struct packed { logic first, second; } s;
    logic [1:0] all;
  } u_t;

  wire u_t x = 2'b10;

  p0: assert property (@(posedge clk) x.s.first == 1);
  p1: assert property (@(posedge clk) x.s.second == 0);
  p2: assert property (@(posedge clk) x.s == 2);
  p3: assert property (@(posedge clk) x.all == 2);

endmodule
