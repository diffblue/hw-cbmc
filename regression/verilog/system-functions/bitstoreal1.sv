module main;

  // Not a conversion, just reinterpretation
  always assert ($bitstoreal(0)==0.0);
  always assert ($bitstoreal('h3ff00000_00000000)==1);
  always assert ($bitstoreal('hc0000000_00000000)==-2.0);

  // good as constant
  parameter p = $bitstoreal(0);

endmodule
