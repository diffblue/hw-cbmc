module BLINK #(localparam CBITS = 11) (input clk, input rst, output reg led, output reg flg);
    reg [CBITS-1:0] cnt;
    reg mode;
    always@(posedge clk, posedge rst) begin
        if (rst) begin
            cnt <= 0;
            mode <= 0;
        end
        else begin
            cnt <= cnt + 1;
            if (cnt == 0)
                mode <= ~mode;
            flg = (cnt == 0);
            led = mode;
        end       
    end
    p1: assert property (@(posedge clk) s_eventually !rst -> led);
    // F G (rst = F) -> G F (led = T)
endmodule
