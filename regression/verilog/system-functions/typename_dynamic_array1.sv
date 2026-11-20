// $typename of dynamic arrays and queues (1800-2017 20.6.1); their
// unpacked dimensions are [] and [$], respectively.
module main;
  bit [7:0] d[];
  int dd[][];
  int du[][4];
  int ud[4][];
  int q[$];
  byte b[];
  string s[];
  logic [3:0][1:0] pd[];
  typedef int dyn_t[];
  dyn_t t;

  p0: assert final ($typename(d) == "bit[7:0]$[]");
  p1: assert final ($typename(dd) == "int$[][]");
  p2: assert final ($typename(du) == "int$[][0:3]");
  p3: assert final ($typename(ud) == "int$[0:3][]");
  p4: assert final ($typename(q) == "int$[$]");
  p5: assert final ($typename(b) == "byte$[]");
  p6: assert final ($typename(s) == "string$[]");
  p7: assert final ($typename(pd) == "logic[3:0][1:0]$[]");
  p8: assert final ($typename(t) == "int$[]");
endmodule
