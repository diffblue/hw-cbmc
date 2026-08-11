// The interface is declared after the module that uses it as a port.
module sub(my_if.slave bus);
  p0: assert property (bus.v == 1);
endmodule

interface my_if;
  logic v;
  initial v = 1;
  modport slave (input v);
endinterface

module main;
  my_if i();
  sub s(i);
endmodule
