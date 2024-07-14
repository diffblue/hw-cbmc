module main;

  wire bit [7:0] x = 'hff;

  // 1800-2017 sec 11.5.1: out-of-bounds bit-select is
  // x for 4-state and 0 for 2-state values.
  property1: assert final (x[7] == 1);
  property2: assert final (x[8] == 0);
  property3: assert final (x[-1] == 0);
  property4: assert final (x[8:7] == 1);
  property5: assert final (x[8:-1] == 'b0111111110);

endmodule
