// Array of interface instances (IEEE 1800-2017 25.3.1)
interface simple_if;
  logic [7:0] data;
endinterface

module main;
  simple_if bus[2]();
  initial bus[0].data = 8'h11;
  initial bus[1].data = 8'h22;
  p1: assert property (bus[0].data == 8'h11);
  p2: assert property (bus[1].data == 8'h22);
endmodule
