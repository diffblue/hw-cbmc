module main;

  parameter P = 20;

  p0: assert property ($bits(10'(1)) == 10);
  p1: assert property ($bits(P'(1)) == 20);
  p2: assert property (10'(-1) == -1);

endmodule
