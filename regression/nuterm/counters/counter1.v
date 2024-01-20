module main(input clk);

  reg [31:0] counter;

  always @(posedge clk)
    if(counter != 0)
      counter = counter - 1;

endmodule
