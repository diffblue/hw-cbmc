module M;
  wire x;
endmodule

module main(input clk);
  M m();
  
  assert property (@(posedge clk) $past(m.x));
  
endmodule
