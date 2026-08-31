// Explicit modport selection in port connection (IEEE 1800-2017 25.5.3)
interface simple_bus;
  logic [7:0] data;
  modport sender(output data);
  modport receiver(input data);
endinterface

module sink(simple_bus.receiver port);
  p1: assert property (port.data == 8'hAB);
endmodule

module main;
  simple_bus sb();
  initial sb.data = 8'hAB;
  sink s(sb.receiver);
endmodule
