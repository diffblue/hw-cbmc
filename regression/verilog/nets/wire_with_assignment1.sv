module main;

  wire x = 2'b10; // truncated
  initial #1 assert($bits(x) == 1 && x == 0);

  wire [1:0] y = 3'b101; // truncated
  initial #1 assert($bits(y) == 2 && y == 1);

  wire signed z = 3'sb100; // truncated
  initial #1 assert($bits(z) == 1 && z == 0);

endmodule
