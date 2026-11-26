// Precedence: ! binds tighter than &&, && tighter than ||, and
// || tighter than -> and <->.
`define A

module main;

`ifdef (!B && A || B)
  p0: assert final (1);
`else
  p0: assert final (0);
`endif

`ifdef (B && B || A)
  p1: assert final (1);
`else
  p1: assert final (0);
`endif

`ifdef (B -> B || A)
  p2: assert final (1);
`else
  p2: assert final (0);
`endif

`ifdef (A -> B -> A)
  p3: assert final (1);
`else
  p3: assert final (0);
`endif

endmodule
