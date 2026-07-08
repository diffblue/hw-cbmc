// Extern method prototype in interface (IEEE 1800-2017 25.4.4)
interface control_if;
  logic enable;

  extern function void set_enable(input logic val);
endinterface

function void control_if::set_enable(input logic val);
  enable = val;
endfunction

module main;
  control_if cif();
  initial cif.set_enable(1);
  p1: assert property (cif.enable == 1);
endmodule
