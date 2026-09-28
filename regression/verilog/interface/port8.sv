// A module drives a member of an interface through a modport port. The
// member of the bound interface instance must then not hold its value.
interface tif;
  logic a;
  logic b;
  modport m(input a, output b);
endinterface

module sub(tif.m s, input clk);
  logic q;
  initial q = 0;
  always_ff @(posedge clk) q <= s.a;
  assign s.b = q;
endmodule

module main(input clk, input v);
  tif i();
  assign i.a = v;
  sub u(.s(i), .clk(clk));

  // q follows v, and hence can become 1
  p0: assert property (@(posedge clk) !u.q);

  // b follows q
  p1: assert property (@(posedge clk) i.b == u.q);
endmodule
