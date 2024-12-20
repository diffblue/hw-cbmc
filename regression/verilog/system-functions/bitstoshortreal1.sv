module main;

  // Not a conversion, just reinterpretation
  always assert ($bitstoshortreal(0)==0.0);
  always assert ($bitstoshortreal('h3f80_0000)==1.0);
  always assert ($bitstoshortreal('hc000_0000)==-2.0);

  // good as constant
  parameter p = $bitstoshortreal(0);

endmodule
