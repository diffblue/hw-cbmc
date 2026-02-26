typedef struct packed {
  logic [99:0] fieldA;
  logic [27:0] fieldB;
} some_type;

module top(output some_type data);

  always_comb begin
    data[63:0] = 0;
    data[127:64] = 2;
    assert(data == 'h2_00000000_00000000);
  end

endmodule
