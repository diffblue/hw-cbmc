module main(Din, En, CLK, Dout);
wire cs;
reg ns;
input CLK;
input Din;
input En;
output Dout;
assign Dout = cs;

always @(Din or cs or En) begin
if (En) begin
 ns = Din;
end
else begin
 ns = cs;
end
assert property1: !En || (ns==Din);
end


ff ff1(.Din(ns), .CLK(CLK), .Dout(cs));
endmodule

module ff(input Din, CLK, output Dout);
reg q;
assign Dout = q;
always @(posedge CLK) begin
q <= Din;
assert property2: (Dout == q);
end
always assert property3: (q == Din) || (q != Din);
endmodule

