// An array of module instances whose interface port is connected to an
// array of interface instances of the same size: 1800-2017 23.3.3.5 binds
// the elements pairwise, left index to left index.
interface pif;
  logic [7:0] a;
endinterface

module sub(pif s, output [7:0] o);
  assign o = s.a;
endmodule

module main;
  pif arr[0:1]();
  assign arr[0].a = 8'd10;
  assign arr[1].a = 8'd11;

  wire [7:0] o0, o1;
  sub s[1:0](.s(arr), .o({o1, o0}));

  // s[1] is bound to arr[0], and s[0] to arr[1]
  p0: assert final (o1 == 8'd10);
  p1: assert final (o0 == 8'd11);
endmodule
