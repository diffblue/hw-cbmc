// Parameterised interfaces are passed on through a chain of interface
// ports, both as a single port and as an array of ports.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module leaf(pif s, pif t[0:1]);
  p0: assert property ($bits(s.a) == 4);
  p1: assert property ($bits(t[0].a) == 4);
  p2: assert property ($bits(t[1].a) == 4);
  p3: assert property (s.a == 4'h5 && t[0].a == 4'h3 && t[1].a == 4'hc);
endmodule

module mid(pif s, pif t[0:1]);
  leaf l(.s(s), .t(t));
endmodule

module main(input clk);
  pif #(.W(4)) i(), a0(), a1();
  assign i.a = 4'h5;
  assign a0.a = 4'h3;
  assign a1.a = 4'hc;
  mid m(.s(i), .t('{a0, a1}));
endmodule
