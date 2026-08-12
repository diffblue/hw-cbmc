module main;

  // Per 1800-2017 11.4.14, the stream_concatenation of a streaming
  // concatenation is a braced list of stream_expression, i.e., it may
  // contain more than one expression.

  // right-to-left, which preserves the order of the operands
  wire [7:0] s1 = {>>{4'ha, 4'hb}};

  // left-to-right with a slice size of 4, which swaps the two nibbles
  wire [7:0] s2 = {<<4{4'ha, 4'hb}};

  initial p1: assert (s1 == 8'hab);
  initial p2: assert (s2 == 8'hba);

endmodule
