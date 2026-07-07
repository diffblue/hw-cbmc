// Named port connection with interface
interface simple_bus;
  logic [7:0] data;
  logic valid;
  initial data = 8'hAB;
  initial valid = 1;
endinterface

module consumer(simple_bus bus);
  p1: assert property (bus.data == 8'hAB);
  p2: assert property (bus.valid == 1);
endmodule

module main(input clk);
  simple_bus my_bus();

  consumer c(.bus(my_bus));
endmodule
