module main(input clk, input [31:0] a);

  always assume a1: 10<=a && a<=100;

  always assert p1: a!=200;

endmodule 
