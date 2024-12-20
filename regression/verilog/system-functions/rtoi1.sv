module main;

  // These truncate
  always assert ($rtoi(1.9)==1);
  always assert ($rtoi(-1.9)==-1);

  // good as constant
  parameter p = $rtoi(1.9);

endmodule
