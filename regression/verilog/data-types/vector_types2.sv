module main;

  localparam p = 1;
  reg [1<<p:0] x;

  assert final ($bits(x)==(1<<p)+1);

endmodule
