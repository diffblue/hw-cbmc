// count up from 0 to 10

module main(
  input logic clk, 
  input logic reset,
  output logic [3:0] counter);

  always_ff @(posedge clk or posedge reset)
    if (reset)
      counter <= 'b0;   
    else if (counter != 10)
      counter <= counter + 1;

  // expected to pass
  ASSERT_COUNTER_EVENTUALLY_10: assert property (@(posedge clk) disable iff (reset) s_eventually (counter == 10));

endmodule
