// A member of an interface is written by a clocked assignment in a
// module, through a port that is passed on by an intermediate module.
interface tif;
  logic [3:0] cnt;
endinterface

module leaf(tif s, input clk);
  initial s.cnt = 0;
  always_ff @(posedge clk) s.cnt <= s.cnt + 1;
endmodule

module mid(tif s, input clk);
  leaf l(.s(s), .clk(clk));
endmodule

module main(input clk);
  tif i();
  mid m(.s(i), .clk(clk));

  // cnt counts up, and hence reaches 3
  p0: assert property (@(posedge clk) i.cnt != 3);

  // the member is the same variable in all scopes
  p1: assert property (@(posedge clk) i.cnt == m.s.cnt && i.cnt == m.l.s.cnt);
endmodule
