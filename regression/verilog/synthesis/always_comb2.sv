module main(input [7:0] data);

  // an 8-bit binary to unary decoder
  reg [255:0] decoded;

  always_comb begin
    integer i;
    for(i = 0; i < 256; i = i + 1)
      decoded[i] = data == i;
  end

  p0: assert property (data == 0 |-> decoded == 1);
  p1: assert property (data == 1 |-> decoded == 2);
  p2: assert property (data == 2 |-> decoded == 4);

endmodule
