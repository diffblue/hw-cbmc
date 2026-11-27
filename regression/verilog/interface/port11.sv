// An interface with an interface port is bound to a module port. The
// members of the interface under the interface port of the interface are
// written through the module port.
interface inner;
  logic [7:0] data;
endinterface

interface outer(inner i);
endinterface

module writer(outer o);
  assign o.i.data = 8'd123;
endmodule

module main;
  inner i();
  outer o(i);
  writer w(o);
  p0: assert final (i.data == 8'd123);
endmodule
