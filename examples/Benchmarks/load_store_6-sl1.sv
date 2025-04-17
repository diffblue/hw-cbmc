module Load_Store (input clk, input rst, output reg sig);
    localparam N = 10000;
    localparam CBITS = 14;
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
    sl1: assert property (@(posedge clk) (always !rst) implies always (m implies (m s_until sig)));
    // G !rst -> G (m -> (m U s))
endmodule
