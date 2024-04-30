module main;

  parameter upper = $;

  reg a, b;

  assert property (a ##[0:upper] b);

endmodule
