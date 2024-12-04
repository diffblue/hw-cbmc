module main(input clk);

  reg [31:0] x = 0;
  always_ff @(posedge clk) x = !x;

  // 1800-2017 16.12.17
  property prop_always(p);
    p and (1 |=> prop_always(p))
  endproperty

  // expected to pass
  assert property (prop_always(x <= 1));

endmodule
