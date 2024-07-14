module main;

  // The type of a parameter is the type of the RHS,
  // unless specified otherwise.

  parameter p1 = 8'h13;
  assert final ($bits(p1) == 8);

  parameter p2 = 'h13;
  assert final ($bits(p2) == 32);

  parameter [9:0] p3 = 'h13;
  assert final ($bits(p3) == 10);

  parameter unsigned [31:0] p4 = -1;
  assert final (p4 == 'hffffffff);

endmodule
