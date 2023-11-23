module main;

  reg clock = 0;

  always #1us clock = ~clock;

endmodule
