module main;

  // x/z are allowed with a four-valued base type
  enum integer { A = 0, B = {32{1'bx}}, C = 1 } enum1;
  enum logic [3:0] { D = 4'b1x0z, E = 3 } enum2;

  // the signing of an integer atom base type is honored
  enum int unsigned { F = 'hffff_ffff } enum3;

  // four-valued base types given by a typedef
  typedef logic [1:0] logic_t;
  typedef integer integer_t;
  enum logic_t { G = 2'bx1, H = 1 } enum4;
  enum integer_t { I = 'z, J = 2 } enum5;

  // expected to pass
  p1: assert final ($bits(A) == 32 && A == 0 && C == 1 && E == 3);
  p2: assert final (F > 0);
  p3: assert final (H == 1 && J == 2);

endmodule
