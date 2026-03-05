module main;

  // SMV identifiers must start with letter or _
  wire \0 = 1;
  wire \$ = 1;
  wire \# = 1;

  // SMV identifiers must not contain +
  wire \foo+bar = 1;

  // deliberately picked to provoke a collision
  wire foo_bar = 1;

  // SMV identifiers must not contain two consecutive dots
  wire \foo..bar = 1;

  // SMV identifiers must not end on a dot
  wire \foo. = 1;

endmodule
