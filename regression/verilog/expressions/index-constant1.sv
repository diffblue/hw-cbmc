module main;

  // index expressions yield constants
  parameter p = 'b1010;
  parameter q = p[3];
  parameter r = p[0];

  assert final (q == 1);
  assert final (r == 0);

endmodule
