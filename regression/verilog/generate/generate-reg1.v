`define BITS 4

module main(input [`BITS-1:0] data);

  reg [`BITS-1:0] result;

  generate
    genvar i;
    for (i = 0; i < `BITS; i=i+1) begin : label
      reg my_reg;

      always @(data) begin : my_generate_block
        my_reg = data[i];
        result[i] = my_reg;
      end
    end
  endgenerate

  // should pass
  always assert p0: result[0] == data[0];
  always assert p1: result[`BITS-1] == data[`BITS-1];

endmodule // main
