// $typename of a packed union (1800-2017 20.6.1). Per the rules there,
// white space is removed except for a single space between identifiers
// and keywords (h), the default signing is removed (b), and a
// user-defined type name is given with its scope (f). The form of the
// name suffix follows the example in 20.6.1 ("struct{bit A;bit B;}top.AB_t").
module main;
  typedef union packed { bit [31:0] a; int signed b; } u_t;
  u_t u;
  p0: assert final ($typename(u) == "union packed{bit[31:0]a;int b;}main.u_t");
endmodule
