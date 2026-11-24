module main(input [15:0] data);

  typedef struct packed {
    logic [5:0] x;
    logic [7:0] y;
    logic [1:0] z;
  } s_t;

  // an unpacked array of packed structs
  s_t a [0:1];
  logic [1:0] z0, z1;

  // Write an element, then read a member of that element, in the same
  // block.
  always_comb begin
    a[0] = data;
    z0 = a[0].z;
    a[1] = ~data;
    z1 = a[1].z;
  end

  p0: assert final (z0 == data[1:0]);
  p1: assert final (z1 == ~data[1:0]);

endmodule
