module sub;

  parameter step = 1;

  typedef enum { E0 = 0 * step, E1 = 1 * step, E2 = 2 * step } my_enumt;

endmodule

module main;

  // The value of enum constants may differ for each module instance.
  sub #(1) sub1();
  sub #(2) sub2();

  p1: assert final (sub1.E0 == 0 && sub1.E1 == 1 && sub1.E2 == 2);
  p2: assert final (sub2.E0 == 0 && sub2.E2 == 2 && sub2.E2 == 4);

endmodule
