interface counter_if;
  reg [3:0] count;
  initial count = 0;
endinterface

module main(input clk);

  counter_if ctr();

  always @(posedge clk) ctr.count = ctr.count + 1;

  // should fail
  p1: assert property (@(posedge clk) ctr.count <= 4'd10);

endmodule
