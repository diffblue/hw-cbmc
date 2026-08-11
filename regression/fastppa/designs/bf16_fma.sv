// BF16 Fused Multiply-Add: result = a*b + c
// BF16: 1 sign, 8 exponent, 7 mantissa (16 bits total)
module bf16_fma(
  input clk,
  input [15:0] a, b, c,
  output reg [15:0] result
);
  // Unpack
  wire a_sign = a[15], b_sign = b[15], c_sign = c[15];
  wire [7:0] a_exp = a[14:7], b_exp = b[14:7], c_exp = c[14:7];
  wire [7:0] a_man = {1'b1, a[6:0]}, b_man = {1'b1, b[6:0]}, c_man = {1'b1, c[6:0]};

  // Multiply: product = a_man * b_man (8x8 -> 16 bits)
  wire prod_sign = a_sign ^ b_sign;
  wire [15:0] prod_man = a_man * b_man;
  wire [8:0] prod_exp = a_exp + b_exp - 9'd127;

  // Align c for addition
  wire [8:0] exp_diff = prod_exp - {1'b0, c_exp};
  wire [15:0] c_man_shifted = (exp_diff < 16) ? ({8'b0, c_man} << (8 - exp_diff)) : 16'd0;

  // Add/subtract
  wire eff_sub = prod_sign ^ c_sign;
  wire [16:0] sum = eff_sub ? ({1'b0, prod_man} - {1'b0, c_man_shifted})
                            : ({1'b0, prod_man} + {1'b0, c_man_shifted});

  // Normalize (find leading one)
  wire [3:0] lz;
  assign lz = sum[16] ? 4'd0 :
              sum[15] ? 4'd1 :
              sum[14] ? 4'd2 :
              sum[13] ? 4'd3 :
              sum[12] ? 4'd4 :
              sum[11] ? 4'd5 :
              sum[10] ? 4'd6 :
              sum[9]  ? 4'd7 :
              sum[8]  ? 4'd8 : 4'd9;

  wire [15:0] norm_man = sum << lz;
  wire [8:0] norm_exp = prod_exp + 9'd1 - {5'b0, lz};

  // Round and pack
  wire [6:0] final_man = norm_man[15:9];
  wire [7:0] final_exp = norm_exp[7:0];
  wire final_sign = (eff_sub && sum[16]) ? ~prod_sign : prod_sign;

  always @(posedge clk) begin
    if(a_exp == 8'd0 || b_exp == 8'd0)
      result <= c; // multiply by zero
    else if(c_exp == 8'd0)
      result <= {prod_sign, prod_exp[7:0], prod_man[13:7]}; // add zero
    else
      result <= {final_sign, final_exp, final_man};
  end
endmodule
