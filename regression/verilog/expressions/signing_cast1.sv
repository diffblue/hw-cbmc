module main;

  // 1800-2017 6.24.1
  p0: assert final (signed'(1'b1) == -1);
  p1: assert final (signed'(4'b1110) == -2);
  p2: assert final (signed'(4'b0111) == 7);
  p3: assert final (signed'(!0) == -1);
  p4: assert final (unsigned'(!0) == 1);
  p5: assert final (unsigned'(-1) == 32'hffff_ffff);

  // signing casts yield constants
  parameter Q = signed'(1);

endmodule
