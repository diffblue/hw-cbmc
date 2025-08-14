module main(input clk);

  reg [2:0] x;

  initial x=0;

  // 0, 1, 2, 3, 3, ...
  always @(posedge clk)
    if(x<3) x++;

  // 4 is never reached, but this doesn't fail the property
  // owing to weak sequence semantics.
  initial p0: assert property (##[*] x==4);

endmodule
