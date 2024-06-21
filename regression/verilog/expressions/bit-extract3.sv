module main;

  wire bit [7:0] x = 'hff;

  // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
  // x for 4-state and 0 for 2-state values.
  always assert property1: x[7] == 1;
  always assert property2: x[8] == 0;
  always assert property3: x[-1] == 0;
  always assert property4: x[8:7] == 1;
  always assert property5: x[8:-1] == 'b0111111110;

endmodule
