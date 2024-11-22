module main(input clk);

  reg [3:0] counter = 0;

  always @(posedge clk)
    if(counter < 10)
      counter++;

  p0: assert property (counter == 0 |-> $past(counter, 1) == 0);
  p1: assert property (counter != 0 && counter != 10 |-> $past(counter, 1) == counter - 1);

endmodule
