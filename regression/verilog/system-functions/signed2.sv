module main;

  p0: assert final ($signed(1) == 1);
  p1: assert final ($signed(1'b1) == -1);
  p2: assert final ($signed(-1) == -1);
  p3: assert final ($signed(!0) == -1);

endmodule
