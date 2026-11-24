module main(input [7:0] d, input [4:0] k, input integer s);

  // Writes with a variable index to unpacked arrays with various declared
  // ranges. Per 1800-2017 7.4.6, a write with an index outside of the
  // declared range performs no operation.
  reg [7:0] q [1:16];  // ascending, offset 1
  reg [7:0] r [15:0];  // descending
  reg [7:0] t [-2:1];  // negative indices
  integer i;

  always @* begin
    for(i = 1; i <= 16; i = i + 1)
      q[i] = 0;
    for(i = 0; i < 16; i = i + 1)
      r[i] = 0;
    for(i = -2; i <= 1; i = i + 1)
      t[i] = 0;
    q[k] = d;
    r[k] = d;
    t[s] = d;
  end

  // in range
  p0: assert final (k == 16 -> q[16] == d);
  p1: assert final (k == 1 -> q[1] == d);
  p2: assert final (k == 0 -> r[0] == d);
  p3: assert final (k == 15 -> r[15] == d);
  p4: assert final (s == -2 -> t[-2] == d);

  // out of range: no element changes
  p5: assert final (k == 0 -> q[16] == 0 && q[1] == 0);
  p6: assert final (k >= 16 -> r[0] == 0 && r[15] == 0);
  p7: assert final ((s < -2 || s > 1) -> t[-2] == 0 && t[1] == 0);

endmodule
