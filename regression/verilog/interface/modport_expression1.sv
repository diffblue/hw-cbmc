// Modport expressions (IEEE 1800-2017 25.5.2)
interface data_if;
  logic [7:0] data;

  modport split(input .upper_half(data[7:4]), input .lower_half(data[3:0]));
endinterface

module consumer(data_if.split port);
  p1: assert property (port.upper_half == 4'hA);
endmodule

module main;
  data_if dif();
  initial dif.data = 8'hAB;
  consumer c(dif);
endmodule
