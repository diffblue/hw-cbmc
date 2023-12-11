module main (input clock);

reg [19:0] a;

initial a = 0;

always @ (posedge clock) begin
  a = a+1;
  // expected to be refuted with k >= 9
  assert p1: a!=10;
end

endmodule
