module main(input clk, input rst);

logic data [1:0];

always_ff @(posedge clk) begin
    data[1] <= 1'b1;
end

assert property(@(posedge clk) disable iff (rst) data[1]);

endmodule

