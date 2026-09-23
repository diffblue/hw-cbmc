module main(input clk);

  // Increasing ranges: index 0 (resp. 4) is the most significant bit.
  reg [0:7] v;
  reg [4:11] u;

  initial v = 0;
  initial u = 0;

  always @(posedge clk)
  begin
    // non-indexed part-select assignment: v[0:3] is the most significant
    // nibble, hence v becomes 8'hA0
    v[0:3] = 4'hA;

    // indexed part-select assignment: for an increasing range v[4+:2]
    // selects the declared indices 4 and 5, i.e. internal bits 3 and 2,
    // hence u/v becomes 8'h0C
    u[8+:2] = 2'b11;
  end

  // v[0:3] is the most significant nibble
  p0: assert property (@(posedge clk) ##1 v == 8'hA0);
  p1: assert property (@(posedge clk) ##1 v[0:3] == 4'hA);
  p2: assert property (@(posedge clk) ##1 v[4:7] == 4'h0);

  // non-zero offset, increasing range: u[8+:2] sets declared indices 8, 9
  p3: assert property (@(posedge clk) ##1 u == 8'h0C);
  p4: assert property (@(posedge clk) ##1 u[8+:2] == 2'b11);

endmodule
