module top(input clock);

  reg [31:0] counter;

  initial counter = 0;

  // This yields
  // 0 1 2 3 4 5 6 7 8 9 3 4 5...
  always @(posedge clock)
    if(counter == 9)
      counter = 3;
    else
      counter = counter + 1;

  // the counter never gets to 10
  p0: assert property (s_eventually counter == 10);

endmodule

