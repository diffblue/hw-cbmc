module sub(input clk);
  reg [7:0] r;
  always @(posedge clk)
    r <= r + 1;
endmodule

module main(input clk);
  sub s(clk);

  initial s.r = 8'd42;

  // s.r is driven both by sub's own always block and, via the
  // hierarchical identifier below, by main's initial block. Should fail
  // once the counter increments past its initial value.
  p0: assert property (@(posedge clk) s.r == 8'd42);
endmodule
