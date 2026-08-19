package my_pkg;
  parameter width = 8;
endpackage

interface my_interface;
  // A package import declaration is a legal interface item,
  // IEEE 1800-2017 A.1.2. The imported "width" is used below.
  import my_pkg::*;
  logic [width-1:0] data;
endinterface

module main;
  my_interface i();
  initial i.data = 255;
  p0: assert final(i.data == 255);
endmodule
