`define W 8
`define R 32

module rf(input clk, input [`W-1:0] data_in, input [`R-1:0] write_enable);

  // index 0 is not used
  reg [`W*`R-1:`W] registers;

  always_ff @(posedge clk) begin
    integer r;
    for(r=1; r<`R; r++)
      if(write_enable[r])
        registers[r*`W+:`W] = data_in;
  end

  always assert property (0);

endmodule
