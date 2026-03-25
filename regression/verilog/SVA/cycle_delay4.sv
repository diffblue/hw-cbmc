// https://github.com/diffblue/hw-cbmc/issues/1756

module zero (input logic clk, req, ack);
    logic val;
    assign val = ack;

    // 1. FAILS: Uses ##0 after a variable-length sequence (should PASS)
    a1: assert property (
        @(posedge clk) req |=> (!ack)[*0:$] ##1 ack ##0 (val == 1)
    );

    // 2. PASSES: Uses logical AND
    a2: assert property (
        @(posedge clk) req |=> (!ack)[*0:$] ##1 ack && (val == 1)
    );

    // 3. FAILS: Uses ##0 after a goto sequence (should PASS)
    b1: assert property (
        @(posedge clk) req |=> ack [->1] ##0 (val == 1)
    );

    // 4. PASSES: Uses overlapping implication
    b2: assert property (
        @(posedge clk) req ##1 ack [->1] |-> (val == 1)
    );
endmodule
