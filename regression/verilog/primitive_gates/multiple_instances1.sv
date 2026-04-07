module main;

  wire w1, w2;

  and a1(w1, 1, 1), a2(w2, 1, 0);

  initial assert(w1==1);
  initial assert(w2==0);

endmodule
