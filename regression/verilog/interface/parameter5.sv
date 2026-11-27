// A defparam on the interface instance that is bound to an interface port.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
endinterface

module pu(pif s);
  localparam N = $bits(s.a);
  p0: assert final (N == 16);
endmodule

module main;
  pif i();
  defparam i.W = 16;
  pu u(.s(i));
endmodule
