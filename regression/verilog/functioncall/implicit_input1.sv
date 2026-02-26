// there is no direction on the port named 'value -- the default is 'input'

function int clog2(int value);
  int tmp;
  tmp = value - 1;
  for (clog2 = 0; tmp>0; clog2 = clog2 + 32'h1)
    tmp = tmp >> 1;
endfunction // clog2

module main;

  test16: assert final(clog2(16) == 4);

endmodule
