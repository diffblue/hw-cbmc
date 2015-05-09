module top (Din, En, CLK, Dout);
  input Din, En, CLK;
  output Dout;

  reg Dout; // sequential
  reg Dout_next; // combinational

  // Combinational block
  always @ ( Din or Dout or En ) begin
    if ( En ) begin
      Dout_next = Din;
    end else begin
      Dout_next = Dout;
    end
  end

  // Sequential block
  always @ ( posedge CLK ) begin
    Dout <= Dout_next;
  end

endmodule
