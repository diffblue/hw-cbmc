package my_pkg;
  parameter my_parameter = 1;
endpackage

import my_pkg::*;

module main;
  assert final(my_parameter == 1);
endmodule
