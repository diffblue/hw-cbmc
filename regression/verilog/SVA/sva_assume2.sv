module main(input a);

  assume property (a implies nexttime a);

  assert property (a |=> $stable(a));

endmodule
