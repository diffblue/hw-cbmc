// An array of interface ports, declared in the body of a module with a
// non-ANSI header (1800-2017 A.2.1.2).
interface bus; logic [3:0] a; modport sink(input a); endinterface
module sub(i, o);
  bus.sink i [1:0];
  output [3:0] o;
  assign o = i[1].a;
endmodule
module main(input clk, input [3:0] x);
  bus u[1:0]();
  assign u[1].a = x;
  wire [3:0] o;
  sub d(.i(u), .o(o));
  p0: assert property (@(posedge clk) o == x);
endmodule
