module observer(input clk);
endmodule

module counter(input clk);
endmodule

module aux(input clk);
  bind counter observer obs(.clk(clk));
endmodule

module main(input clk);
  // The instance of counter is elaborated before the bind
  // directive in aux is seen.
  counter c(clk);
  aux a(clk);
endmodule
