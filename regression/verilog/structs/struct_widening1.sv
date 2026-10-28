module main(input [15:0] x);

  typedef struct packed {
    logic [7:0] hi;
    logic [7:0] lo;
  } s_t;

  typedef logic [1:0][7:0] bytes_t;

  // assigning a narrower part-select zero-extends it
  s_t s1, s2, s3;
  assign s1 = x[7:0];
  always_comb s2 = x[7:0];
  always_comb s3 = s_t'(x[11:4]);

  // part-selects that fit
  s_t s4;
  assign s4 = {x[3:0], x[15:4]};

  // conversions between aggregates
  bytes_t b;
  s_t s5;
  assign b = x;
  assign s5 = s_t'(b);

  p1: assert final (s1.hi == 0 && s1.lo == x[7:0]);
  p2: assert final (s2.hi == 0 && s2.lo == x[7:0]);
  p3: assert final (s3.hi == 0 && s3.lo == x[11:4]);
  p4: assert final (s4.hi == {x[3:0], x[15:12]} && s4.lo == x[11:4]);
  p5: assert final (s5.hi == x[15:8] && s5.lo == x[7:0]);
  p6: assert final (s1.lo == 0);

endmodule
