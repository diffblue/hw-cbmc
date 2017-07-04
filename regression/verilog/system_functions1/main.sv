module main;

  localparam N=10;
  wire [(N-1):0] some_sig;

  localparam clog_out = $clog2(1);
  always assert ($clog2(1)==1 && $clog2(2)==1 && $clog2(3)==2);
  always assert ($bits(some_sig)==10);

endmodule
