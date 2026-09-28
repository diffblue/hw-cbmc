// An array of module instances with interface ports, 1800-2017 23.3.2.
// The interface instances are bound to every element of the array,
// whereas the vector connection is split over the elements (23.3.3).
interface pif;
  logic [3:0] a;
endinterface

module sub(pif s, pif t[0:1], input [3:0] k);
  p1: assert property (s.a == 4'd5);
  p2: assert property (t[0].a == 4'd3 && t[1].a == 4'd7);
  p3: assert property (k == 4'd1 || k == 4'd2);
endmodule

module main;
  pif i(), a0(), a1();
  assign i.a = 4'd5;
  assign a0.a = 4'd3;
  assign a1.a = 4'd7;

  sub s[1:0](.s(i), .t('{a0, a1}), .k({4'd1, 4'd2}));
endmodule
