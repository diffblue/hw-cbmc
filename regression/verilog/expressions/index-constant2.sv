module main;

  // index expressions yield constants
  parameter p = (1>0); // boolean
  parameter q = p[0];

  assert final (q == 1);

endmodule
