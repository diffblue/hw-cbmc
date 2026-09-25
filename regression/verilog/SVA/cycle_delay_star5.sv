module main(input clk);

  // saturating counter
  reg [3:0] c = 0;

  always @(posedge clk)
    if(c != 15)
      c <= c + 1;

  // 1800-2017 16.9.2: ##[*] is equivalent to ##[0:$].  The sequence
  // c==1 ##[*] c==1 hence matches with zero delay at t=1.
  // Expected to pass.
  p0: assert property (@(posedge clk) c == 1 |-> strong(c == 1 ##[*] c == 1));

endmodule
