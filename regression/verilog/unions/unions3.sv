module main;

  union packed {
    // a struct inside a union
    struct packed {
      bit [7:0] field1;
    } field1;

    bit [7:0] field2;
  } u;

  initial begin
    u.field1.field1 = 123;
  end

  // Expected to pass.
  p1: assert property (u.field2 == 123);

endmodule
