interface myInterface;
  int i;
endinterface

module main;

  myInterface interface_instance();

  initial interface_instance.i = 123;

endmodule
