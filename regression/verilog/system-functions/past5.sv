module main;

  logic [31:0] mem[123];

  assert property (mem == $past(mem));

endmodule
