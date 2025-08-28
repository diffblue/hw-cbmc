module main(input a);

  assume property (a);

  initial assert property (s_eventually a);

endmodule
