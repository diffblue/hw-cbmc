module main (i, clock);
input i, clock;
reg [19:0] a,b,c;

initial a = 1;
initial b = 5;
initial c = 7;

always @ (posedge clock) begin
  a <= b;
  b <= c;
  c <= a;
  assert p1: a==1 || a==5 || a==7;
end

endmodule
