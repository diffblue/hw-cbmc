module Load_Store (input clk, input rst, output reg sig);
    localparam N = 5000;
    localparam CBITS = 13;
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

  // LTLSPEC G (Verilog.Load_Store.rst = FALSE) -> G  (((Verilog.Load_Store.m = TRUE) -> (Verilog.Load_Store.m = TRUE U Verilog.Load_Store.sig = TRUE)))
  assert property (@(posedge clk) (always !rst) implies always (m implies (m s_until sig)));

endmodule