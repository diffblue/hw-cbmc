module main;

  // padded from left with zeros
  wire [6*8-1:0] hello = "hello";
  always assert p0: hello[0*8+7:0*8] == "o";
  always assert p1: hello[1*8+7:1*8] == "l";
  always assert p2: hello[2*8+7:2*8] == "l";
  always assert p3: hello[3*8+7:3*8] == "e";
  always assert p4: hello[4*8+7:4*8] == "h";
  always assert p5: hello[5*8+7:5*8] == 0;

endmodule
