module main;

  always assert ($itor(1)==1.0);
  always assert ($itor(-1)==-1.0);

  // good as constant
  parameter p = $itor(1);

endmodule
