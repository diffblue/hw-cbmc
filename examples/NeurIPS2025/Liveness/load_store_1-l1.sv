module Load_Store (input clk, input rst, output reg sig);
    localparam N = 750;
    localparam CBITS = 10;
    reg [CBITS-1:0] vol;
    reg m;
    always @(posedge clk) begin
        if (rst) begin m = 0; vol = 0; sig = 0;
        end else begin
            if (m) begin
                if (vol >= N) m = 0; else vol = vol + 1;
            end else begin
                if (vol <= 0) m = 1; else vol = vol - 1;
            end
            if (vol >= N) begin
                sig = 1;
                vol = N;
            end
            else
                sig = 0; 
        end 
    end

  // LTLSPEC F G (Verilog.Load_Store.rst = FALSE) -> G F (Verilog.Load_Store.sig = TRUE)
  assert property (@(posedge clk) s_eventually !rst -> sig);

endmodule