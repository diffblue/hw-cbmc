// return statements inside loops, IEEE 1800-2017 12.8
module main(input clk, input c, input [2:0] n);

  function automatic int f(input int limit, input bit flag);
    for (int i = 0; i < 4; i++) begin
      if (flag) return 100;
      if (i == limit) return i;
    end
    return -1;
  endfunction

  reg [3:0] count;

  task t(input bit flag);
    count = 0;
    for (int i = 0; i < 4; i++) begin
      if (flag && i == 2) return;
      count = count + 1;
    end
    count = 15;
  endtask

  always @(posedge clk) begin
    p0: assert (f(2, c) == (c ? 100 : 2));
    p1: assert (f(10, 0) == -1);
    p2: assert (f(n, c) == (c ? 100 : (n < 4 ? n : -1)));
    t(c);
    p3: assert (count == (c ? 2 : 15));
    p4: assert (1);
  end
endmodule
