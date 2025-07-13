module main(input a);

  initial p0: assert property ((s_eventually a) or (always !a));
  initial p1: assert property ((s_eventually a) or not ##[*] a);
  initial p2: assert property ((##[*] a) or (always !a));

endmodule
