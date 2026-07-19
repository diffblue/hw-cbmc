module main;

  initial assert($typename(logic)=="logic");
  initial assert($typename(logic[31:0])=="logic[31:0]");
  initial assert($typename(logic unsigned[0:31])=="logic[0:31]");
  initial assert($typename(logic signed[31:0])=="logic signed[31:0]");

endmodule
