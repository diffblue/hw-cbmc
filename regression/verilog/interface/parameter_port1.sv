// Parameterized interface passed through port (IEEE 1800-2017 25.8)
interface param_if #(parameter W = 8);
  logic [W-1:0] data;
endinterface

module consumer(param_if bus);
  p1: assert property (bus.data == 32'hCAFEBABE);
endmodule

module main;
  param_if #(32) wide();
  initial wide.data = 32'hCAFEBABE;
  consumer c(wide);
endmodule
