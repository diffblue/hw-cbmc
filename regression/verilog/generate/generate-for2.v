`define BITS 4

module main(input [`BITS-1:0] data);

  reg [`BITS-1:0] result;

  generate
    genvar i;
    for (i = 0; i < `BITS; i=i+1) begin
      always @(data) result[i] = data[i];
    end
  endgenerate

  /* equivalent to
  always @(data) result[0] = data[0];
  always @(data) result[1] = data[1];
  always @(data) result[2] = data[2];
  always @(data) result[3] = data[3];
  */

  // should pass
  always assert p0: result[0] == data[0];
  always assert p1: result[`BITS-1] == data[`BITS-1];

endmodule // main
