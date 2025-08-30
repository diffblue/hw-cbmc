module main;

  typedef struct {
    bit some_bit;
  } inner_struct;

  typedef struct {
    bit [31:0] array [123];
    bit other_bit;
    inner_struct inner;
  } my_struct;

  my_struct s;

  assert property (s == $past(s));

endmodule
