// An interface port without a modport, declared in the body of a module
// with a non-ANSI header (1800-2017 A.2.1.2).
interface bus; logic a; endinterface
module sub(i, o);
  bus i;
  output o;
  assign o = i.a;
endmodule
module main(input clk, input a);
  bus u(); assign u.a = a;
  wire o;
  sub d(.i(u), .o(o));
  p0: assert property (@(posedge clk) o == a);
endmodule
