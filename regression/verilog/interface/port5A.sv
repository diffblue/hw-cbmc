// The interface used by this module is declared in port5B.sv, which is
// given later on the command line.
module sub(my_if bus);
  p0: assert property (bus.v == 1);
endmodule
