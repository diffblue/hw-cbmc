// A parameterised interface with a parameter override is bound to the
// interface port of every element of an array of module instances.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module sub(pif s, input [3:0] k);
  p0: assert property ($bits(s.a) == 4);
  p1: assert property (s.a == 4'd5);
  p2: assert property (k == 4'd1 || k == 4'd2);
endmodule

module main;
  pif #(.W(4)) i();
  assign i.a = 4'd5;

  sub s[0:1](.s(i), .k({4'd1, 4'd2}));
endmodule
