module main;

  wire clk;
  localparam WIDTH = 8 - 1;

  reg [WIDTH:0] counter;
  always @(posedge clk) counter = counter + 1;

  always assert p1: $bits(counter)==8;

endmodule
