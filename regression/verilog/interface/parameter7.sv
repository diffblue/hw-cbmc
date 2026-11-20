// A chain of interfaces that use each other through their interface
// ports, declared in the reverse order of their dependencies.
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

interface B(A a);
  logic [7:0] e;
  assign e = a.d;
endinterface

interface C(B b);
  logic [7:0] f;
  assign f = b.e;
endinterface

module main(input [7:0] x);
  C c(.b(b));
  B b(.a(a));
  A #(.W(8)) a();
  assign a.d = x;
  p0: assert final (c.f == x);
  p1: assert final ($bits(c.b.a.d) == 8);
endmodule
