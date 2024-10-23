module main;

  // part-select expressions yield constants
  parameter p = 'b1010;
  parameter q = p[3:1];
  parameter r = p[1 +: 3];

  assert final (q == 'b101);
  assert final (r == 'b101);

endmodule
