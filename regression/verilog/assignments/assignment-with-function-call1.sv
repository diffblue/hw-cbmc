module top(input [7:0] a, input [7:0] b);

  function [2:0] fn;
  input [2:0] x, y;
  begin
    fn = x + y;
  end
  endfunction

  wire [7:0] sum_a_b = fn(a, b),
             sum_1_2 = fn(1, 2),
             sum_2_3 = fn(2, 3);

  assert property (sum_a_b[2:0]==a[2:0]+b[2:0]);

  assert property (sum_1_2==3);

  assert property (sum_2_3==5);

endmodule
