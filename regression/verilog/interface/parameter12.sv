// An interface with an interface port is bound to a module port. The
// interface under the module port has an interface port with the
// parameters of the innermost instance, whose members are connected.
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

interface B(A a);
  logic [$bits(a.d)-1:0] copy;
endinterface

module pu(B b);
  assign b.a.d = 16'h1234;
  p0: assert final ($bits(b.copy) == 16);
  p1: assert final ($bits(b.a.d) == 16);
endmodule

module main;
  pu u(.b(b));
  B b(.a(a));
  A #(.W(16)) a();
  p2: assert final (a.d == 16'h1234);
endmodule
