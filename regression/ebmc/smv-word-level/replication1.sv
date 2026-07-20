module main;

  wire [3:0] a = 4'hA;
  wire [7:0] rep = {2{a}};
  wire [11:0] rep3 = {3{a}};

endmodule
