// The example from issue #2353
module top(input wire a, output reg y);
  task automatic copy(input reg x, output reg z);
    z = x;
  endtask
  always @* copy(a, y);
endmodule
