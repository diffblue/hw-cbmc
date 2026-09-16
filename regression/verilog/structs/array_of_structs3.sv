module main;

  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;

  pair_t a [3];
  logic [15:0] b [3];

  pair_t c [2];
  logic [15:0] d [2];

  // 1800-2017 6.22.1: the two element types have the same number of bits
  // and the same signing, and hence the unpacked arrays are of equivalent
  // types.  The first member of a packed struct is the most significant,
  // and the array element with index zero is the first element.
  initial begin
    a[0].hi = 8'h01; a[0].lo = 8'h02;
    a[1].hi = 8'h03; a[1].lo = 8'h04;
    a[2].hi = 8'h05; a[2].lo = 8'h06;

    b = a;

    p0: assert (b[0] == 16'h0102);
    p1: assert (b[1] == 16'h0304);
    p2: assert (b[2] == 16'h0506);
  end

  // the same in the other direction
  initial begin
    d[0] = 16'h1122;
    d[1] = 16'h3344;

    c = d;

    p3: assert (c[0].hi == 8'h11 && c[0].lo == 8'h22);
    p4: assert (c[1].hi == 8'h33 && c[1].lo == 8'h44);
  end

endmodule
