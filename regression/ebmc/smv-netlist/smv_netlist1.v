module main(input clk);

  reg \my-bit ;

  always @(posedge clk)
    \my-bit = !\my-bit ;

  initial \my-bit = 0;

endmodule
