module main;

  struct packed {
    bit [7:0] a, b;
  } s[2];

  initial begin
    s = '{ '{ 1, 2 }, '{ 3, 4 } };

    // Expected to pass.
    // Icarus Verilog says this is 16
    p0: assert($bits(s) == 2 * 2 * 8);

    p0a: assert(s[0].a == 1);
    p0b: assert(s[0].b == 2);
    p1a: assert(s[1].a == 3);
    p1b: assert(s[1].b == 4);
  end

endmodule
