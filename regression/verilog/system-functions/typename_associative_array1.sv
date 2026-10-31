// $typename of associative arrays (1800-2017 20.6.1). The expected
// strings follow the convention for unpacked arrays ($ in place of the
// name, then the dimensions), with the index type in the brackets; they
// need checking against the standard.
module main;
  int aa[int];
  int aw[*];
  bit [7:0] as[string];
  p0: assert final ($typename(aa) == "int$[int]");
  p1: assert final ($typename(aw) == "int$[*]");
  p2: assert final ($typename(as) == "bit[7:0]$[string]");
endmodule
