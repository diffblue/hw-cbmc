// Boolean expressions in `ifdef (IEEE 1800-2023 22.6)
`define A
`define B

module main;

`ifdef (A && B)
  p0: assert final (1);
`else
  p0: assert final (0);
`endif

`ifdef (A && !C)
  p1: assert final (1);
`else
  p1: assert final (0);
`endif

`ifdef (C || (A && B))
  p2: assert final (1);
`else
  p2: assert final (0);
`endif

`ifdef (C -> A)
  p3: assert final (1);
`else
  p3: assert final (0);
`endif

`ifdef (A <-> C)
  p4: assert final (0);
`else
  p4: assert final (1);
`endif

`ifndef (A && C)
  p5: assert final (1);
`else
  p5: assert final (0);
`endif

`ifdef (C)
  p6: assert final (0);
`elsif (A && B)
  p6: assert final (1);
`else
  p6: assert final (0);
`endif

endmodule
