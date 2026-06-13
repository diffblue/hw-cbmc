module main;

  // 1800-2017 11.4.12
  // "Unsized constant numbers shall not be allowed in concatenations"
  wire [31:0] x = { '1 };

endmodule
