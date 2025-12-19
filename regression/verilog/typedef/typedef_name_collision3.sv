module sub;


endmodule

module main;

  wire some_identifier;

  // name collision
  sub some_identifier();

endmodule
