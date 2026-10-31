// $typename of packed and unpacked unions (1800-2017 20.6.1). The
// expected strings follow EBMC's convention for structs; they need
// checking against the standard.
module main;
  typedef union packed { bit [1:0] a; bit [1:0] b; } pu_t;
  pu_t pu;
  p0: assert final ($typename(pu) == "union{bit[1:0] a;bit[1:0] b;}");
endmodule
