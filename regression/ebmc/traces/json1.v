module main(input clk);

  reg [31:0] data;
  initial data = 1;

  always @(posedge clk)
    data = data + 1;

  always assert p1: data == 1;

endmodule
