class myClass;
  int unqualified;
  const int max_size = 100;
  static int count;
  protected int hidden;
  local bit secret;
  rand logic [7:0] mode;
  randc logic [1:0] cycle;
endclass

module main;
  myClass c = null;
endmodule
