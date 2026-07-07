interface myInterface;
  int i;
  initial i = 123;
endinterface

module sub(myInterface bus);
  always @(bus.i)
    assert(bus.i == 123);
endmodule

module main;

  myInterface interface_instance();
  sub sub_inst(interface_instance);
endmodule
