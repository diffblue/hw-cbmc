package my_package;
  function automatic logic inv(input logic x);
    return ~x;
  endfunction
endpackage

interface my_interface;
  // IEEE 1800-2017 26.3: package import; 25.3: interface bodies may contain
  // package import declarations, making the imported symbols visible in
  // interface scope.
  import my_package::*;
  logic a, b;
  always_comb b = inv(a);
endinterface

module main(input clk);
  my_interface i ();
endmodule
