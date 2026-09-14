module producer(input clk);
  reg [3:0] cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;
endmodule

module consumer(input clk);
  wire [3:0] probe;

  // Upward name referencing (1800-2017 23.8): starting from the
  // top-level module name, descend into a sibling instance.
  assign probe = top.prod.cnt;

  // probe mirrors the sibling's counter
  p_ok: assert property (@(posedge clk) probe == top.prod.cnt);

  // the counter is not constantly zero
  p_bad: assert property (@(posedge clk) probe == 0);
endmodule

module top(input clk);
  producer prod(.clk(clk));
  consumer cons(.clk(clk));
endmodule
