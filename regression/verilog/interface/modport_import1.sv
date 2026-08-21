interface my_interface;
  logic [1:0] data;

  function automatic logic parity(input logic [1:0] x);
    return ^x;
  endfunction

  // IEEE 1800-2017 25.7: a modport can import interface tasks/functions
  modport m (input data, import parity);
endinterface

module main(input clk);
  my_interface i ();
endmodule
