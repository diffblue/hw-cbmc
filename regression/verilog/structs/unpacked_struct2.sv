module main;

  // an unpacked struct type
  typedef struct {
    bit field;
  } s_type;

  // bit-vectors cannot be assigned to unpacked structs
  wire s_type w = 123;

endmodule
