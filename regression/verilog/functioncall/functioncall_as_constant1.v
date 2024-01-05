module main;

  function [31:0] clog2;
  input [63:0] value;
  reg [63:0] tmp;
  begin
    tmp = value - 1;
    for (clog2 = 0; tmp>0; clog2 = clog2 + 32'h1)
      tmp = tmp >> 1;
  end
  endfunction // clog2

  parameter param16 = clog2(16);
  parameter param17 = clog2(17);
  
  always assert test_param16: param16 == 4;
  always assert test_param17: param17 == 5;

endmodule
