module main;

  // an unpacked struct
  struct {
    bit field;
  } s;

  // unpacked structs cannot be converted to bit-vectors
  wire [8:0] w = s;

endmodule
