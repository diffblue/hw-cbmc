module main(input signed [7:0] a, b);

  // -128 / -1 overflows: +128 is not representable in 8 signed bits.
  // Per 1800-2017 6.9.1, arithmetic is modulo 2^n, yielding -128.
  initial assert (8'sh80 / 8'shff == 8'sh80);

  initial assert (a == 8'sh80 && b == 8'shff -> a / b == a);

endmodule
