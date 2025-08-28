module main;

  property P;
    1
  endproperty

  // This should be rejected -- && is for expressions
  assert property (P && P);

endmodule
