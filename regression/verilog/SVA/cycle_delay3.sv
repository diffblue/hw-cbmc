// https://github.com/diffblue/hw-cbmc/issues/1747

module top (input logic clk, pause);

    // Assumption: If pause is high, it MUST go low within the next 3 cycles.
    // This makes 4 consecutive high cycles impossible.
    pause_window: assume property (@(posedge clk) pause |-> ##[1:3] !pause );

    // Assertion: Checks for the impossible condition (4 consecutive high cycles).
    never_4pauses: assert property (@(posedge clk) pause [*4] |-> 1'b0 );

endmodule
