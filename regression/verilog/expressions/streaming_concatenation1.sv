module main;

  // reverse bits
  assert final ({<<{4'b1010}} == 4'b0101);

  // works on booleans
  assert final ({<<{(1 == 1)}} == 1);

  // reverse nibbles
  assert final ({<<4{16'habcd}} == 16'hdcba);

  // reverse bytes
  assert final ({<<8{16'habcd}} == 16'hcdab);

endmodule
