function [31:0] logval;
  input [63:0]                   value;
  reg [63:0]                     tmp;
  begin
    tmp = value - 1;
    for (logval = 0; tmp > 0; logval = logval + 32'h1)
      tmp = tmp >> 1;
  end
endfunction // clogval2
