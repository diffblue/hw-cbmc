module main;

  function [31:0] clog2;
  input [63:0]                   value;
  reg [63:0]                     tmp;
  begin
    tmp = value - 1;
    for (clog2 = 0; tmp>0 ; clog2 = clog2 + 32'h1)
     tmp = tmp >> 1;
    end
  endfunction // clog2

  wire [clog2(16):1] x4='hff; // 4 bits
  wire [clog2(17):1] x5='hff; // 5 bits
  
  always assert test1: x4=='b1111;
  always assert test2: x5=='b11111;

endmodule
