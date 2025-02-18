module main(input clk);

  reg [7:0] x, y = 30;

  initial x=20;

  always_ff @(posedge clk) x=5;
  always_ff @(posedge clk) y=6;

  // fails, owing to nondeterministic initial state
  p1: assert property (x==20 || x==5);

  // fails, owing to nondeterministic initial state
  p2: assert property (y==30 || y==6);

endmodule 
