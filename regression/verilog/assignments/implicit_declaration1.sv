module main;

  // 1800-2017 6.10: continuous assignment statements can trigger an
  // implicit declaration of a "scalar net of default net type".
  assign some_net0 = 'b10;
  assign some_net1 = 'b11;

  initial assert($bits(some_net0) == 1 && some_net0 == 0);
  initial assert($bits(some_net1) == 1 && some_net1 == 1);

endmodule
