module main(input clk);

  reg ping = 0, pong = 0;

  always @(posedge clk) begin
    ping <= !ping;
    pong <= ping;
  end

  // system functions in a named property
  property p;
    @(posedge clk) $rose(ping) |-> ##1 pong;
  endproperty

  assert property (p);

endmodule
