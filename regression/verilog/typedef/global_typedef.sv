// The VIS model checker accepts global-scoped typedefs as an extension of
// Verilog. These are at the top-level scope, which is not permitted by
// SystemVerilog.  It is not clear whether these are file-local or not.

typedef bit [31:0] some_word_type;

module sub(data_in, data_out);
  input some_word_type data_in;
  output some_word_type data_out;

  // just echo it back
  always @data_in data_out = data_in;

endmodule

module main;

   wire some_word_type data_in, data_out;

   sub s(data_in, data_out);

   p0: assert property (data_in == data_out);

endmodule
