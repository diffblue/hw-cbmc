module main;

  int A[10:1];
  int B[0:9];
  byte C[10:1];
  int D[1:10];
  int E[2][3];
  int F[0:1][1:3];

  initial begin
    for(int i = 0; i < 10; i++) B[i] = i * 100 + 1;
    A = B; // left-to-right: A[10] = B[0], A[9] = B[1], ...
    C = B; // truncation to byte
    D = A; // D[1] = A[10]
    for(int i = 0; i < 2; i++) for(int j = 0; j < 3; j++) F[i][j+1] = i * 10 + j;
    E = F;
  end

  p0: assert final (A[10] == 1);
  p1: assert final (A[9] == 101);
  p2: assert final (A[1] == 901);
  p3: assert final (C[10] == 8'd1);
  p4: assert final (C[9] == 8'(101));
  p5: assert final (C[1] == 8'(901));
  p6: assert final (D[1] == 1);
  p7: assert final (D[10] == 901);
  p8: assert final (E[0][0] == 0);
  p9: assert final (E[1][2] == 12);
  p10: assert final (E[1][0] == 10);

endmodule
