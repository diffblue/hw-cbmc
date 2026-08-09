module main(input clk);

  reg [7:0] count;

  initial count = 0;

  always @(posedge clk) count = count + 1;

  sub my_sub(.clk(clk), .data(count));

endmodule
