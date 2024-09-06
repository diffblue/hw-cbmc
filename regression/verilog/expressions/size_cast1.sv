module main;

  parameter P = 20;

  p0: assert final ($bits(10'(1)) == 10);
  p1: assert final ($bits(P'(1)) == 20);
  p2: assert final (10'(-1) == -1);
  p3: assert final (2'(1==1) == 1);

endmodule
