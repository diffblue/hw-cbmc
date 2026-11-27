// An interface port declared in the body of a module with a non-ANSI
// header, with a modport.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
  modport m(input a);
endinterface

module pu(s);
  pif.m s;
  localparam N = $bits(s.a);
  p0: assert final (N == 16);
endmodule

module main;
  pif #(.W(16)) i();
  pu u(.s(i));
endmodule
