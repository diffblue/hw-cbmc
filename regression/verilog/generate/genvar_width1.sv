module main;
  for (genvar i=0; i<1; i++) begin : g
    p: assert final ($bits(i) == 32);
  end
endmodule
