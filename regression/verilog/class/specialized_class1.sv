class stack #(int DEPTH = 8);
  int mem[DEPTH];
endclass

module main;
  stack #(16) s = null;
endmodule
