// Interface scope resolution operator (IEEE 1800-2017 25.3)
interface bus_if;
  typedef logic [7:0] byte_t;
  byte_t data;
endinterface

module main;
  bus_if bus();
  bus_if::byte_t temp;
  initial begin
    temp = 8'hAB;
    bus.data = temp;
  end
  p1: assert property (bus.data == 8'hAB);
endmodule
