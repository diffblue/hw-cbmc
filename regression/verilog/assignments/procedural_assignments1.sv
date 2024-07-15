module main(input [31:0] in);

  reg [31:0] data;

  always @in begin
    data = 1;
    a01: assert(data == 1);

    data++;
    a02: assert(data == 2);

    data--;
    a03: assert(data == 1);

    data <= in; // non-blocking
    a04: assert(data == 1);

    data += 10;
    a05: assert(data == 11);

    data -= 10;
    a06: assert(data == 1);

    data *= 5;
    a07: assert(data == 5);

    data /= 2;
    a08: assert(data == 2);

    data %= 3;
    a09: assert(data == 2);

    data &= 3;
    a10: assert(data == 2);

    data |= 1;
    a11: assert(data == 3);

    data ^= 1;
    a12: assert(data == 2);

    data <<= 1;
    a13: assert(data == 4);

    data >>= 1;
    a14: assert(data == 2);

    data <<<= 1;
    a15: assert(data == 4);

    data >>>= 1;
    a16: assert(data == 2);

  end

endmodule
