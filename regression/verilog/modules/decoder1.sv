// Example of a recursive module instantiation

module decoder#(parameter N = 4) (input [N-1:0] binary, output [2**N-1:0] unary);

  generate
    if(N==1)
      assign unary = binary;
    else begin
      // generate one N-1 bit decoder recursively
      wire [2**(N-1)-1:0] output_rec;
      decoder #(N-1) decoder_rec(binary[N-2:0], output_rec);
      wire top = binary[N-1];
      assign unary = {output_rec & {2**(N-1){top}}, output_rec & {2**(N-1){!top}}};
    end
  endgenerate

endmodule

module decoder_tb;

  wire [15:0] unary;
  decoder decoder1(4'd5, unary);
  p0: assert final (unary == 'b0000_0000_0001_0000); // 16

endmodule
