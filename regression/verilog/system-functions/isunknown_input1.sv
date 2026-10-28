// An input port of a four-state type may carry x or z (IEEE 1800-2017
// 6.3.1, 23.2.2); one of a two-state type never does.
module main(input logic [3:0] in4, input bit [3:0] in2);
  p0: assert final ($isunknown(in4) == 0);
  p1: assert final ($isunknown(in2) == 0);
endmodule
