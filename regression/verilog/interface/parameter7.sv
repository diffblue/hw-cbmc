// Parameterised interfaces passed on through interface ports: a module
// passes its interface port on to a submodule, and an interface with an
// interface port is bound to a module port.
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

interface B(A a);
  logic [$bits(a.d)-1:0] e;
  assign e = a.d;
endinterface

module leaf(A p, output [7:0] y);
  assign y = p.d;
endmodule

module mid(A q, output [7:0] y);
  leaf l(.p(q), .y(y));
endmodule

module reader(B b, output [7:0] z);
  assign z = b.e;
  p0: assert final ($bits(b.a.d) == 8);
endmodule

module main(input [7:0] x);
  A #(.W(8)) a();
  B b(.a(a));
  wire [7:0] y, z;
  mid m(.q(a), .y(y));
  reader r(.b(b), .z(z));
  assign a.d = x;
  p1: assert final (y == x);
  p2: assert final (z == x);
  p3: assert final ($bits(b.e) == 8);
endmodule
