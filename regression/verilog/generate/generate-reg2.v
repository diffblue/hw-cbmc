`define BITS 4

module main(input [`BITS-1:0] data);

  reg [`BITS-1:0] result;

  generate
    if(1) begin
      reg [`BITS-1:0] my_reg;
      always @(data) begin
        my_reg = data;
        result = my_reg;
      end
    end
  endgenerate

  // should pass
  always assert p0: result[0] == data[0];
  always assert p1: result[`BITS-1] == data[`BITS-1];

endmodule // main
