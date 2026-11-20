// An interface port declared in the module body, but not in the port list.
interface bus; logic a; modport sink(input a); endinterface
module sub(input x);
  bus.sink i;
endmodule
