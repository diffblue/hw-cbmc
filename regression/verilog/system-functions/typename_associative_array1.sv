// $typename of associative arrays (1800-2017 20.6.1): "$" is the
// placeholder for the name of the anonymous unpacked array (d), followed
// by the dimension, here with the index type; no white space (h).
module main;
  int aa[int];
  int aw[*];
  bit [7:0] as[string];
  p0: assert final ($typename(aa) == "int$[int]");
  p1: assert final ($typename(aw) == "int$[*]");
  p2: assert final ($typename(as) == "bit[7:0]$[string]");
endmodule
