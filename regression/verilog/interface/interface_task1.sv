interface bus_if;
  logic [7:0] data;

  task set_data(input logic [7:0] d);
    data = d;
  endtask
endinterface

module main;
  bus_if bus();
  initial bus.set_data(8'hFF);
  p1: assert property (bus.data == 8'hFF);
endmodule
