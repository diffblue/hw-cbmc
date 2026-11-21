module main;

  // 1800-2017 11.4.11: the conditional operator on aggregates and reals
  // when the condition is ambiguous (x/z). When the operands are
  // logically equivalent, the result is either operand.

  typedef struct { int a; logic [3:0] b; } us_t;
  typedef struct packed { logic [3:0] a; bit [3:0] b; } ps_t;
  typedef union packed { logic [7:0] a; bit [7:0] b; } pu_t;

  us_t us1 = '{a: 1, b: 4'b0011}, us2 = '{a: 2, b: 4'b0011};
  ps_t ps1 = 8'h35, ps2 = 8'h56;
  pu_t pu1 = 8'h0f, pu2 = 8'h1e;
  bit [1:0][3:0] pa1 = 8'h12, pa2 = 8'h36;
  int ua1 [0:1] = '{1, 2}, ua2 [0:1] = '{1, 4};
  us_t uas1 [0:1] = '{'{a: 1, b: 1}, '{a: 2, b: 2}};
  us_t uas2 [0:1] = '{'{a: 1, b: 1}, '{a: 3, b: 2}};
  real r1 = 1.5, r2 = 2.5;
  bit [3:0] a = 4'b1100;

  // Integral operands, including packed aggregates, are combined bit by
  // bit; a bit that differs is x.
  p0: assert final ((1'bx ? ps1 : ps2) === 8'b0xx101xx);

  // The aggregates are modelled two-valued, and hence, x is 0 when the
  // result has the aggregate type.
  ps_t ps_x;
  pu_t pu_x;
  bit [1:0][3:0] pa_x;
  assign ps_x = 1'bx ? ps1 : ps2;
  assign pu_x = 1'bx ? pu1 : pu2;
  assign pa_x = 1'bx ? pa1 : pa2;
  p1: assert final (ps_x == 8'h14 && ps_x.a == 4'h1);
  p2: assert final (pu_x == 8'h0e);
  p3: assert final (pa_x == 8'h12 && pa_x[1] == 4'h1);

  // Unpacked arrays are combined element by element. An element that
  // does not match is the value given by Table 7-1 for its type. For
  // other unpacked aggregates, the result is the value given by Table 7-1
  // for the type.
  us_t us_x;
  int ua_x [0:1];
  us_t uas_x [0:1];
  assign us_x = 1'bx ? us1 : us2;
  assign ua_x = 1'bx ? ua1 : ua2;
  assign uas_x = 1'bx ? uas1 : uas2;
  p4: assert final (us_x.a == 0 && us_x.b == 0);
  p5: assert final (ua_x[0] == 1 && ua_x[1] == 0);
  p6: assert final (uas_x[0].a == 1 && uas_x[1].a == 0 && uas_x[1].b == 0);

  // The result for reals that differ is 0.
  p7: assert final ((1'bx ? r1 : r2) == 0.0);
  p8: assert final ((1'bx ? r1 : r1) == r1);

  // A Boolean result
  p9: assert final (!(1'bx ? a == a : a != a));
  p10: assert final (1'bx ? a == a : a == a);

  // A condition with a known 1 bit is true, and one with all bits 0 is
  // false.
  p11: assert final ((2'b1x ? us1 : us2) == us1);
  p12: assert final ((2'bz1 ? r1 : r2) == r1);
  p13: assert final ((2'b00 ? us1 : us2) == us2);

  // logically equivalent unpacked operands
  p14: assert final ((1'bx ? us1 : us1) == us1);
  p15: assert final ((1'bx ? ua1 : ua1) == ua1);

endmodule
