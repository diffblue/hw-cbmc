// A module passes its interface port on to a submodule; the module is
// instantiated before the parameterized interface instance that is bound
// to its port.
interface A #(parameter W = 1);
  logic [W-1:0] d;
endinterface

module leaf(A p, output [7:0] y);
  assign y = p.d;
endmodule

module mid(A q, output [7:0] y);
  leaf l(.p(q), .y(y));
endmodule

module main(input [7:0] x);
  wire [7:0] y;
  mid m(.q(a), .y(y));
  A #(.W(8)) a();
  assign a.d = x;
  p0: assert final (y == x);
endmodule
