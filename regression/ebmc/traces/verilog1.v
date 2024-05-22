module main(input clk);

  parameter P = 123;
  parameter Q = P + 1;

  reg [31:0] data;
  initial data = 1;

  always @(posedge clk)
    data = data + 1;

  always assert p1: data != 10;

endmodule
