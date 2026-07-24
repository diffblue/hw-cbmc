module main;

  typedef struct { int x; } my_struct_type;
  parameter my_struct_type P = '{ x: 123 };

  parameter Q = P.x;

endmodule
