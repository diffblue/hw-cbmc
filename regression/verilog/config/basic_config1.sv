module SUB;
  parameter P = 1;
endmodule

module top;
  SUB sub();
endmodule

config some_config;
  design top;
  instance top.sub use #(.P(2));
endconfig

