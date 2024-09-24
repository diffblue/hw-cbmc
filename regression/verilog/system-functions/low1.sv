module main;

  logic [7:0] mask;

  genvar i;
  generate
    for (i=$low(mask); i<=$high(mask); i = i + 1)
      always_comb @* mask[i] = (i%2)==1;
  endgenerate

  assert final (mask == 'b10101010);

endmodule
