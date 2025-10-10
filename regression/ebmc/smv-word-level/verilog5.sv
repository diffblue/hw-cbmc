module main(input clk, input in);

  p1: assert property (in iff s_nexttime $past(in));

endmodule
