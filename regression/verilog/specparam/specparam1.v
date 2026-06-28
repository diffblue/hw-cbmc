module main(input clk, input d, output reg q);

  specparam tpd = 1.5;
  specparam tsu = 0.5, thd = 0.3;

  always @(posedge clk)
    q <= d;

endmodule
