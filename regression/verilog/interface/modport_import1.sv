// Modport with import (IEEE 1800-2017 25.5.4)
interface data_if;
  logic [7:0] data;

  function logic [7:0] get();
    return data;
  endfunction

  modport consumer(input data, import get);
endinterface

module reader(data_if.consumer port);
  p1: assert property (port.get() == 8'hAB);
endmodule

module main;
  data_if dif();
  initial dif.data = 8'hAB;
  reader r(dif);
endmodule
