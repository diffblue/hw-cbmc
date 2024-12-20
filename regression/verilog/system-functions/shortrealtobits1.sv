module main;

  // Not a conversion, just reinterpretation
  always assert ($shortrealtobits(0.0)==0);
  always assert ($shortrealtobits(1.0)=='h3f80_0000);
  always assert ($shortrealtobits(-2.0)=='hc000_0000);

  // good as constant
  parameter p = $shortrealtobits(0.0);

endmodule
