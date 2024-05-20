module main(input clk);

  reg [31:0] counter;

  always @(posedge clk)
    if(counter != 0)
      counter = counter - 1;

  wire \$live = counter == 0;

endmodule
