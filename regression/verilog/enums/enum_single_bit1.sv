module main(input clk);

  // enums with a single-bit base type
  enum bit { B0, B1 } b = B0;
  enum logic { L0, L1 } l = L0;

  always @(posedge clk) begin
    if(b == B0) b <= B1; else b <= B0;
    if(l == L0) l <= L1; else l <= L0;
  end

  // expected to pass
  p0: assert property (B0 == 0 && B1 == 1 && L0 == 0 && L1 == 1);
  p1: assert property (b == B0 || b == B1);
  p2: assert property (~l == (l == L0));

  // expected to fail
  p3: assert property (b != B1);

endmodule
