module main;

  logic [31:0] mem[123];

  assert property (##1 mem == $past(mem));

endmodule
