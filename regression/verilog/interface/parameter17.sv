// Interface ports connected implicitly, by a wildcard, and by name
// next to a wildcard.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module pu(pif s, pif t);
  p0: assert final ($bits(s.a) == 16);
  p1: assert final ($bits(t.a) == 4);
endmodule

module main;
  pif #(.W(16)) s();
  pif #(.W(4)) t(), other();
  pif #(.W(2)) unused();
  pu u1(.*);
  pu u2(.s, .t);
  pu u3(.t(other), .*);
endmodule
