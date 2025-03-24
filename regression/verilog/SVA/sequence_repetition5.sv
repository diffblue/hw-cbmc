module main(input clk, input data);

  reg [31:0] x = 0;

  always_ff @(posedge clk)
    if(x == 9 || (x >= 1 && data))
      x = 0;
    else
      x++;

  wire pulse = x == 0;

  // should pass
  initial p0: assert property (pulse ##1 !pulse[*1:9] ##1 pulse);

  // should fail
  initial p1: assert property (pulse ##1 !pulse[*1:8] ##1 pulse);

endmodule
