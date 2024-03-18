module main;

  struct packed {
    // a struct inside a struct
    struct packed {
      bit [7:0] field1;
    } field1;
  } s;

  initial begin
    s.field1.field1 = 123;
  end

  // Expected to pass.
  p1: assert property (s.field1.field1 == 123);

endmodule
