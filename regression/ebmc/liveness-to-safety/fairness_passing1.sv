module main(input clk, input a, input b);

  reg x, seen_a;

  initial x=0;
  initial seen_a=0;

  always @(posedge clk) begin
    if(a) seen_a <= 1;
    if(b && seen_a) x <= 1;
  end

  assume property (always s_eventually a);
  assume property (always s_eventually b);

  // expected to pass, owing to the two fairness assumptions
  p0: assert property (s_eventually x);

endmodule
