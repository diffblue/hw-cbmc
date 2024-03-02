module main(input clk);

  reg [31:0] counter;

  initial counter=0;

  always @(posedge clk)
    if(counter == 5)
      counter = 5;
    else
      counter=counter+1;

  // both expected to fail
  p0: assert property (s_eventually counter==0);
  p1: assert property (s_eventually counter==6);

endmodule
