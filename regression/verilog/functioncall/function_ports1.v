module main;

  function [31:0] clog2(input [63:0] value);
  reg [63:0] tmp;
  begin
    tmp = value - 1;
    for (clog2 = 0; tmp>0; clog2 = clog2 + 32'h1)
      tmp = tmp >> 1;
  end
  endfunction // clog2

  wire [31:0] clog2_of_16 = clog2(16);

  always assert test16: clog2_of_16 == 4;

endmodule
