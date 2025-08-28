module main;

  property P;
    1
  endproperty

  // This is an error -- P is used as an expression
  wire x = P;

endmodule
