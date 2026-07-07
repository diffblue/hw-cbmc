interface myInterface;
  int i;
  initial i = 123;
endinterface

module main;

  myInterface interface_instance();

  always @(interface_instance.i)
    assert(interface_instance.i == 123);

endmodule
