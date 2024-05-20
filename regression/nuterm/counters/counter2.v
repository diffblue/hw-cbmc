module main(input clk);

  reg [31:0] counter;

  always @(posedge clk)
    if(counter < 100)
      counter = counter + 1;
    else
      counter = 0;

  wire \$live = counter == 0;

endmodule
