module main(input clk);

  wire [31:0] x = 10;

  sequence x_is_ten;
    x == 10 ##1 x >= 0
  endsequence : x_is_ten

  assert property (x_is_ten);

  sequence x_is_twenty;
    // the ; is optional
    x == 20;
  endsequence : x_is_twenty

endmodule
