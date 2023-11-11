module my_module#(BITS = 32)(input clk);

  reg [BITS-1:0] counter;
  always @(posedge clk) counter = counter + 1;

endmodule

module main;

  wire clk;
  my_module #(8) m8(clk);

endmodule
