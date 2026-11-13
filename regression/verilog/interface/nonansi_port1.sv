// Interface ports with a modport, declared in the body of a module with a
// non-ANSI header (1800-2017 A.2.1.2), including a list of such ports.
interface bus;
  logic [7:0] a, b;
  modport sink (input a, output b);
endinterface
module sub(clk, i, j, o);
  input clk;
  bus.sink i, j;
  output [7:0] o;
  assign o = i.a ^ j.a;
  assign i.b = ~i.a;
endmodule
module main(input clk, input [7:0] a, input [7:0] c);
  bus b1(), b2();
  assign b1.a = a;
  assign b2.a = c;
  wire [7:0] o;
  sub u(.clk(clk), .i(b1), .j(b2), .o(o));
  p0: assert property (@(posedge clk) o == (a ^ c));
  p1: assert property (@(posedge clk) b1.b == ~a);
  p2: assert property (@(posedge clk) o == a);   // fails
endmodule
