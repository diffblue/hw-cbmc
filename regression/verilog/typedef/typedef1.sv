module main;

   typedef bit [31:0] some_word_type;
   typedef bit signed [31:0] some_signed_type;

   some_word_type some_word;
   some_signed_type some_signed;

   p0: assert final ($bits(some_word) == 32);

endmodule
