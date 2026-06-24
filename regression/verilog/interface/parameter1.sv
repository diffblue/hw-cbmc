interface myInterface #(parameter WIDTH = 8);
  logic [WIDTH-1:0] data;
endinterface

module main;

  myInterface #(.WIDTH(16)) wide_bus();

  initial wide_bus.data = 16'hCAFE;

endmodule
