module main;

  // Not a conversion, just reinterpretation
  always assert ($realtobits(0.0)==0);
  always assert ($realtobits(1.0)=='h3ff00000_00000000);
  always assert ($realtobits(-2.0)=='hc0000000_00000000);

  // good as constant
  parameter p = $realtobits(0.0);

endmodule
