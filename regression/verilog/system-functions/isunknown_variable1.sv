// $isunknown applied to four-state variables that hold x or z
// (IEEE 1800-2017 6.3.1, 20.9).
module main(input clk, input int idx);
  logic [3:0] a = 4'b1x00;     // declaration initializer
  logic [3:0] b;               // initial block
  initial b = 4'b10z0;
  logic [3:0] c = 0;           // assigned x on the clock
  logic [3:0] u;               // never assigned: x (6.8, Table 6-7)
  integer i = 'x;
  reg [3:0] r = 4'bxxxx;
  typedef struct packed { logic [1:0] f; logic g; } s_t;
  s_t s = '{f: 2'b1x, g: 1'b0};
  logic [3:0] k = 4'b1010;
  logic [3:0] m [0:3] = '{default: 4'b0000};

  always @(posedge clk) begin
    a <= a;
    b <= b;
    c <= 4'bx;
    i <= i;
    r <= r;
    s <= s;
    k <= k;
    m <= m;
  end

  p0: assert property (@(posedge clk) $isunknown(a) == 1);
  p1: assert property (@(posedge clk) $isunknown(b) == 1);
  p2: assert property (@(posedge clk) ##1 $isunknown(c) == 1);
  p3: assert property (@(posedge clk) $isunknown(u) == 1);
  p4: assert property (@(posedge clk) $isunknown(i) == 1 && $isunknown(r) == 1);
  p5: assert property (@(posedge clk) $isunknown(s) == 1 && $isunknown(s.g) == 0);
  // x propagates through operators, but not through x & 0 (11.4)
  p6: assert property (@(posedge clk)
        $isunknown(a + 4'd1) == 1 && $isunknown(a & 4'b0000) == 0 &&
        $isunknown(a[2]) == 1 && $isunknown(a[3]) == 0);
  // reading out of bounds yields x (7.4.6, 11.5.1)
  p7: assert property (@(posedge clk) idx == 5 -> $isunknown(k[idx]) == 1);
  p8: assert property (@(posedge clk) idx == 7 -> $isunknown(m[idx]) == 1);
  // the usual X check fails
  p9: assert property (@(posedge clk) !$isunknown(a));
endmodule
