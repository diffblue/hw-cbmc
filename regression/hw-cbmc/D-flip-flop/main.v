module top(Din, En, CLK, Dout);
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
  end

  //ff ff1(ns, CLK, cs);
  ff ff1(.Din(ns), .CLK(CLK), .Dout(cs));

endmodule

module ff(input Din, CLK, output Dout);
  input CLK;
  input Din;
  output Dout;

  reg q;
  assign Dout = q;

  always @(posedge CLK) begin
    q <= Din;
  end

endmodule
