// Two modules connected through a shared interface
interface data_if;
  logic [3:0] value;
  initial value = 1;
endinterface

module writer(data_if bus);
  initial bus.value = 2;
endmodule

module reader(data_if bus);
  initial p0: assert(bus.value == 1 || bus.value == 2);
endmodule

module main(input clk);
  data_if shared();

  writer w(shared);
  reader r(shared);
endmodule
