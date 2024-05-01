module main;
  wire w;
  p1: assert property (s_eventually w);
  p2: assert property (s_eventually !w);
endmodule
