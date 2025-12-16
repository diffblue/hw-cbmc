module main(input clk);

  wire [31:0] x = 10;

  property x_is_ten;
    x == 10
  endproperty : x_is_ten

  // Cannot be used as a sequence, even when it syntactically
  // qualifies as a sequence.
  sequence some_sequence;
    x_is_ten
  endsequence

  initial assert(some_sequence);

endmodule
