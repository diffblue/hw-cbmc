module main;

  // part-select expressions yield constants
  parameter p = 'b1010;
  parameter q = p[3:1];

  assert final (q == 'b101);

endmodule
