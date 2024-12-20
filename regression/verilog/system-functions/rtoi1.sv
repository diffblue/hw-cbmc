module main;

  // These truncate
  always assert ($rtoi(1.9)==1);
  always assert ($rtoi(-1.9)==-1);

endmodule
