checker myChecker(input logic [31:0] data1, input logic [31:0] data2);
  assert property (data1 != data2);
endchecker

module main(input clk);
  reg [31:0] counter = 0;
  always_ff @(posedge clk) counter++;
  myChecker c(counter, 10);
endmodule
