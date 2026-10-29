// A parameterised interface with a parameter override is bound to the
// interface ports of an array of module instances. The interfaces under
// the ports of every element take the parameters of the bound instances.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module sub(pif s, pif t[0:1]);
  p0: assert property ($bits(s.a) == 4);
  p1: assert property ($bits(t[0].a) == 4 && $bits(t[1].a) == 4);
  p2: assert property (s.a == 4'd5 && t[0].a == 4'd3 && t[1].a == 4'd7);
endmodule

module main;
  pif #(.W(4)) i(), a0(), a1();
  assign i.a = 4'd5;
  assign a0.a = 4'd3;
  assign a1.a = 4'd7;

  sub s[0:1](.s(i), .t('{a0, a1}));
endmodule
