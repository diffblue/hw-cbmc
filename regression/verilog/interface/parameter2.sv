// A parameterised interface with a parameter override is bound to a
// modport port, by name and by position. The interface under the port
// takes the parameters of the bound instance.
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
  pif #(.W(4)) i(), j();
  pu u(.s(i));
  pu v(j);
  assign i.a = '1;
  assign j.a = 4'b0101;

  p1: assert property (@(posedge clk) i.b == 4'b1111);
  p2: assert property (@(posedge clk) j.b == 4'b0101);
endmodule
