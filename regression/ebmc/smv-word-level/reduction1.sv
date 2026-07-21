module main;

  wire [7:0] a = 8'hA5;
  wire r_and = &a;
  wire r_or = |a;
  wire r_xor = ^a;
  wire r_nand = ~&a;
  wire r_nor = ~|a;
  wire r_xnor = ~^a;

endmodule
