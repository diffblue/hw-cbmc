module my_module#(COUNT = 128)(input clk);

  reg [$clog2(COUNT)-1:0] counter;
  always @(posedge clk) counter = counter + 1;

endmodule

module main;

  wire clk;
  my_module #(8) m8(clk);
  my_module #(16) m16(clk);

  always assert p1: $bits(m8.counter)==3;
  always assert p2: $bits(m16.counter)==4;

endmodule
