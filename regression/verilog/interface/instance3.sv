interface myBus;
  logic [7:0] data;
  logic valid;
endinterface

module main;

  myBus bus1();
  myBus bus2();

  initial bus1.data = 8'hAB;
  initial bus2.valid = 1;

endmodule
