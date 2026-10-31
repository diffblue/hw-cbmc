// $test$plusargs and $value$plusargs in conditions
// (sv-tests 21.6--test, 21.6--value). EBMC assumes that no plusargs
// are given.
module main(input clk);
  bit a, b, c = 0;
  int v;

  initial begin
    if($test$plusargs("TEST")) a = 1; else a = 0;
    b = $test$plusargs("TEST") ? 1 : 0;
    v = 7;
    if($value$plusargs("V=%d", v)) v = 1;
  end

  always @(posedge clk)
    if($test$plusargs("TEST")) c = 1;

  p0: assert property (@(posedge clk) a == 0 && b == 0);
  p1: assert property (@(posedge clk) v == 7);
  p2: assert property (@(posedge clk) c == 0);
endmodule
