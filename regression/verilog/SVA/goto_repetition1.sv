// https://github.com/diffblue/hw-cbmc/issues/1750

module goto(input logic clk, req);

    logic ack = 1'b0;

    // This is refuted 
    assert_goto: assert property (@(posedge clk) req |=> ack[->1]);

    // This is equivalent, but proved up to bound
    assert_equivalent: assert property ( @(posedge clk) req |=> (!ack)[*0:$] ##1 ack);

endmodule
