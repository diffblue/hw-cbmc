module main(input increment);

  wire clk;
  reg [31:0] some_reg = 0;

  always @(posedge clk)
    if(increment)
      some_reg = some_reg + 1;

endmodule
