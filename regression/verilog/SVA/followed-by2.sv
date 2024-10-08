module main(input clk, input a, input b);

  // equivalences from 1800 2017 16.12.9
  p0: assert property ((a #-# b) iff (not (a |-> not b)));
  p1: assert property ((a #=# b) iff (not (a |=> not b)));

endmodule
