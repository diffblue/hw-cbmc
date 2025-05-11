module main;

   nettype logic [31:0] some_word_type;
   nettype logic signed [31:0] some_signed_type;

   some_word_type some_word;
   some_signed_type some_signed;

   p0: assert final ($bits(some_word) == 32);

endmodule
