module BLINK #(localparam CBITS = 28) (input clk, input rst, output reg led, output reg flg);
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

  // LTLSPEC F G (Verilog.BLINK.rst = FALSE) -> G F (Verilog.BLINK.led = TRUE)
  assert property (@(posedge clk) s_eventually !rst -> led);

endmodule