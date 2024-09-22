module main(input clk);

  reg [7:0] counter;

  initial counter = 0;

  // 0, 1, 2, 3, 4, 0, ...
  always @(posedge clk)
    if(counter < 5)
      counter = counter + 1;
    else
      counter = 0;

  // expected to pass, owing to the first disjunct
  p0: assert property ((s_eventually counter==1) or (s_eventually counter==10));

endmodule
