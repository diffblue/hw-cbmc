module main(input clk);

  reg [31:0] counter;

  initial counter=0;

  always @(posedge clk)
    counter=counter+1;

  // both expected to pass
  p0: assert property (eventually counter==0);
  p1: assert property (eventually counter==8);

endmodule
