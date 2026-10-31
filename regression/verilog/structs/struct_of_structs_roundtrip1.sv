module main(input [7:0] a, input [7:0] b);

  typedef struct packed {
    logic [3:0] tag;
    logic [3:0] val;
  } e_t;

  typedef struct packed {
    e_t x;
    e_t y;
  } p_t;

  p_t p;
  logic [15:0] w;
  logic [3:0] r0, r1;

  always_comb begin
    // write the members, read the whole struct as a bit-vector,
    // and convert it back
    p.x = e_t'(a);
    p.y = e_t'(b);
    w = p;
    p = p_t'(w);
    r0 = p.x.val;
    r1 = p.y.tag;
  end

  p1: assert final (w == {a, b});
  p2: assert final (r0 == a[3:0] && r1 == b[7:4]);
  p3: assert final (r0 == 0);

endmodule
