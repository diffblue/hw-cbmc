// 1800-2017 A.4.1.1 / 23.3.2.3: a named port connection may omit the
// parenthesized expression when the port name and the identifier to be
// connected coincide, i.e. ".clk_i" is shorthand for ".clk_i(clk_i)".
// Regression for LogikBench blocks/{hmac,i2c,spi,uart}, large/{cva6,aes,
// wally}, which use this idiom pervasively for clock/reset ports.
module sub(input clk_i, input rst_ni, output q_o);

  assign q_o = clk_i & rst_ni;

endmodule

module main(input clk_i, input rst_ni, output q_o);

  sub u_sub(.clk_i, .rst_ni, .q_o);

endmodule
