module main(input clk);

  reg ping = 0, pong = 0;

  always @(posedge clk) begin
    ping <= !ping;
    pong <= ping;
  end

  // system functions in a named sequence
  sequence s;
    $rose(ping) ##1 pong;
  endsequence

  assert property (@(posedge clk) $rose(ping) |-> s);

endmodule
