module main;

  property P;
    1
  endproperty

  // This should be rejected
  wire x = P + P;

endmodule
