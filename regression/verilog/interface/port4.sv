// The formal name in a named port connection lives in the port name
// space of the instantiated module, and hence may coincide with the
// name of an interface.
module sub(input logic data_if);
  initial p0: assert(data_if == 1);
endmodule

interface data_if;
  logic value;
  initial value = 1;
endinterface

module main;
  data_if shared();

  sub s(.data_if(shared.value));
endmodule
