module main(input clk);
  reg [31:0] x;

  initial x=1;
  always_ff @(posedge clk)
    if(x<10)
      x++;

  // should pass
  p0: assert property (x >= 1 && x <= 10);

endmodule
