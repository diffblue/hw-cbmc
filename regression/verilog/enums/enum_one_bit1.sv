module top();
  enum logic {g = 0, h = 1} v1;
  enum bit {i = 0, j} v2;
  typedef enum logic {A, B} ab_t;
  ab_t v3;

  always_comb begin
    v1 = h;
    v2 = j;
    v3 = B;
  end

  p1: assert final (g == 0 && h == 1 && j == 1 && B == 1);
  p2: assert final (v1 == h && v2 == j && v3 == B);
endmodule
