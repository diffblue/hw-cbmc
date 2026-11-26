module main;

  // 1800-2017 5.9: a string literal can be assigned to an unpacked
  // array of bytes; if the size differs, it is left justified
  byte b1[3:0] = "hi2";
  byte b2[0:2] = "abcd";
  bit [7:0] b3[1:2] = "xy";
  logic [7:0] b4[2] = "z";

  initial begin
    p0: assert(b1[3] == "h" && b1[2] == "i" && b1[1] == "2" && b1[0] == 0);
    p1: assert(b2[0] == "a" && b2[1] == "b" && b2[2] == "c");
    p2: assert(b3[1] == "x" && b3[2] == "y");
    p3: assert(b4[0] == "z" && b4[1] == 0);
  end

endmodule
