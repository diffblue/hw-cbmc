module main;

  struct packed {
    int field;
  } s;

  int data;

  // @ allows a "hierarchical event expression" without parentheses
  always @s.field
    data = s.field;

endmodule
