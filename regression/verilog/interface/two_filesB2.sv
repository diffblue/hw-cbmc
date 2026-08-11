interface some_if;
  logic ack;
endinterface

module sub(bus_if bus);
  always @(bus.i)
    assert(bus.i == 123);
endmodule

module main;
  bus_if interface_instance();
  sub sub_inst(interface_instance);
endmodule
