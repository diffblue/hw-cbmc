module top(input clk);

  reg [7:0] counter;

  always @(posedge clk) counter++;

  // our reset condition is counter!=0, so this one holds
  initial assert property (@(posedge clk) counter != 0);

endmodule
