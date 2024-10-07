module main;

  wire some_wire;

  // some_wire is not a constant
  typedef enum bit [7:0] { A = some_wire } enum_t;

endmodule
