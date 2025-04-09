module main(input clk);

  reg x;

  initial x = 0;

  always @(posedge clk)
    x = !x;

  always assert property (always s_eventually x);

endmodule
