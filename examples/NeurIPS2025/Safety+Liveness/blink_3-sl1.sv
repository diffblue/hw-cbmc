module BLINK #(localparam CBITS = 10) (input clk, input rst, output reg led, output reg flg);
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

  // LTLSPEC G Verilog.BLINK.rst = FALSE -> G ( Verilog.BLINK.led = TRUE -> (Verilog.BLINK.led = TRUE U Verilog.BLINK.mode = FALSE))
  assert property (@(posedge clk) !rst implies always (led implies (led s_until !mode)));

endmodule