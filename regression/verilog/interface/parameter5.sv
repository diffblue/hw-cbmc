// An interface with an interface port, bound to a parameterized interface
// instance that is declared after it. The instances are parameterized in
// the order of their interface port connections, not in source order.
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

interface B(A a);
  logic [7:0] e;
  assign e = a.d;
endinterface

module main(input [7:0] x);
  B b(.a(a));
  A #(.W(8)) a();
  assign a.d = x;
  p0: assert final (b.e == x);
  p1: assert final ($bits(b.a.d) == 8);
endmodule
