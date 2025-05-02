module main(input clk);

  reg [7:0] counter = 0;

  always @(posedge clk)
    counter++;

  initial p0: assert property (##0 $past(counter, 0) == 0);
  initial p1: assert property (##1 $past(counter, 1) == 0);
  initial p2: assert property (##2 $past(counter, 2) == 0);
  initial p3: assert property (##3 $past(counter, 3) == 0);
  initial p4: assert property (##4 $past(counter, 4) == 0);

  initial q0: assert property (##0 $past(counter, 1) == 0);
  initial q1: assert property (##1 $past(counter, 1) == 0);
  initial q2: assert property (##2 $past(counter, 1) == 1);
  initial q3: assert property (##3 $past(counter, 1) == 2);
  initial q4: assert property (##4 $past(counter, 1) == 3);

endmodule
