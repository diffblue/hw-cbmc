module sub(input [7:0] data [2]);

  initial p0: assert (data[0] == 8'hab);
  initial p1: assert (data[1] == 8'hcd);

endmodule

module main;

  typedef struct packed { logic [7:0] f; } byte_t;

  byte_t arr [2];

  // 1800-2017 6.22.1: byte_t is a packed struct that is 4-state, unsigned
  // and 8 bits wide, and hence is an equivalent type to [7:0].  Unpacked
  // arrays with the same size and equivalent element types are equivalent
  // in turn, and hence arr can be connected to the port.
  sub s(.data(arr));

  initial begin
    arr[0].f = 8'hab;
    arr[1].f = 8'hcd;
  end

endmodule
