// $test$plusargs and $value$plusargs in conditions
// (sv-tests 21.6--test, 21.6--value). EBMC assumes that no plusargs
// are given.
module main(input clk);
  bit a, b, c = 0;
  int v, n, m, k;

  initial begin
    if($test$plusargs("TEST")) a = 1; else a = 0;
    b = $test$plusargs("TEST") ? 1 : 0;
    v = 7;
    if($value$plusargs("V=%d", v)) v = 1;

    // break in a branch, which makes the path conditions differ
    n = 0;
    for(int i = 0; i < 4; i++) begin
      if($test$plusargs("X")) break;
      n++;
    end

    // in a loop guard
    k = 0;
    for(int i = 0; i < 4 && !$test$plusargs("SKIP"); i++) k++;
  end

  always @(posedge clk)
    if($test$plusargs("TEST")) c = 1;

  always @(posedge clk) begin
    m = 0;
    for(int i = 0; i < 4; i++) begin
      if($test$plusargs("X")) break;
      m++;
    end
  end

  p0: assert property (@(posedge clk) a == 0 && b == 0);
  p1: assert property (@(posedge clk) v == 7);
  p2: assert property (@(posedge clk) c == 0);
  p3: assert property (@(posedge clk) n == 4 && k == 4);
  p4: assert property (@(posedge clk) ##1 m == 4);
endmodule
