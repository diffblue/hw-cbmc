module main;

  typedef struct {
    bit [31:0] f1, f2;
  } my_struct;

  wire my_struct s;

  assign s.f1 = 1;
  assign s.f2 = 2;

  assert final (s.f1 == 1);
  assert final (s.f2 == 2);

endmodule
