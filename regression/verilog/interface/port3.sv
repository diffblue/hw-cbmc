// Two modules connected through a shared interface
interface data_if;
  logic [3:0] value;
  initial value = 4'd7;
endinterface

module writer(data_if bus);
  p1: assert property (bus.value == 4'd7);
endmodule

module reader(data_if bus);
  p1: assert property (bus.value == 4'd7);
endmodule

module main(input clk);
  data_if shared();

  writer w(shared);
  reader r(shared);
endmodule
