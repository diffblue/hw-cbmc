// An interface that instantiates another interface, 1800-2017 25.3.
// The inner instance takes its parameter from that of the outer interface.
interface inner #(parameter W = 2);
  logic [W-1:0] x;
endinterface

interface outer #(parameter W = 4);
  inner #(W * 2) i();
endinterface

module main(input [15:0] in);
  outer #(8) o();

  assign o.i.x = in;

  p0: assert final ($bits(o.i.x) == 16);
  p1: assert final (o.i.x == in);
endmodule
