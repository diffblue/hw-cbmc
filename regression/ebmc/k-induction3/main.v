module main (input clock);

reg [19:0] a;

initial a = 0;

always @ (posedge clock) begin
  a = a+1;
  assert p1: a!=10;
end

endmodule
