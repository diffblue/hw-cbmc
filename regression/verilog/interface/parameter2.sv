// A parameterised interface with a parameter override is bound to a
// modport port. The interface under the port takes the parameters of
// the bound instance.
interface pif #(parameter W = 8);
  logic [W-1:0] a;
  logic [W-1:0] b;
  modport m(input a, output b);
endinterface

module pu(pif.m s);
  assign s.b = s.a;
  p0: assert property ($bits(s.a) == 4);
endmodule

module main(input clk);
  // the interface instance is declared after the module that uses it
  pu u(.s(i));
  pif #(.W(4)) i();
  assign i.a = '1;

  p1: assert property (@(posedge clk) i.b == 4'b1111);
endmodule
