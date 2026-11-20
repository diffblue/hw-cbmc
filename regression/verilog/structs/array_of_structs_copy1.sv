module main(input [7:0] a);

  typedef struct packed {
    logic [3:0] tag;
    logic [3:0] val;
  } e_t;

  e_t [3:0] q, t;
  logic [3:0] r1, r2, r3;

  always_comb begin
    // write whole elements, then copy the whole array
    for(int i = 0; i < 4; i++)
      q[i] = '{tag: 4'(a[3:0] + i), val: a[7:4]};
    t = q;
    r1 = t[1].tag;
    r2 = q[1].tag;
    r3 = t[3].val;
  end

  p1: assert final (t[0] == q[0] && t[1] == q[1] && t[2] == q[2] && t[3] == q[3]);
  p2: assert final (r1 == 4'(a[3:0] + 1));
  p3: assert final (r2 == 4'(a[3:0] + 1));
  p4: assert final (r3 == a[7:4]);
  p5: assert final (r1 == 0);

endmodule
