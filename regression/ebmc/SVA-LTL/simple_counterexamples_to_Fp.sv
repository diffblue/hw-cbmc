module top(input clock);

  reg [31:0] constant;
  reg [31:0] counter;

  initial constant = 123;
  initial counter = 0;

  always @(posedge clock)
    if(counter < 5)
      counter = counter + 1;

  // false never becomes true
  p0: assert property (s_eventually 0);

  // the constant is never 1
  p1: assert property (s_eventually constant == 1);

  // the counter never gets to 6
  p2: assert property (s_eventually counter == 6);

endmodule

