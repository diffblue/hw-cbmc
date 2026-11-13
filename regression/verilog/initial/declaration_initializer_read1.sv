// The initializer of a variable declaration takes effect before any
// initial or always procedure starts (1800-2017 6.8, 10.5), so an initial
// block that reads the variable sees the initial value.
module main;
  int n = 0;
  logic [3:0] l = 4'd3;
  int k = 0;
  int a = 2;
  int b;

  initial n = n + 1;
  initial l = l + 1;
  initial for(int i = 0; i < 4; i++) k++;
  initial b = a;

  p0: assert final (n == 1);
  p1: assert final (l == 4);
  p2: assert final (k == 4);
  p3: assert final (b == 2);
endmodule
