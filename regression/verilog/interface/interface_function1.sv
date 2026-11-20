// Function defined in interface, called via hierarchical name (IEEE 1800-2017 25.4)
interface math_if;
  logic [7:0] value;

  function logic [7:0] double();
    return value * 8'd2;
  endfunction
endinterface

module main;
  math_if m();
  initial m.value = 8'd21;
  p1: assert property (m.double() == 8'd42);
endmodule
