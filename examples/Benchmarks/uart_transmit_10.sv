module UART_T #(localparam d_width = 15, c_width = 5) (input clk, input rst, input tx_ena, input [d_width - 1: 0] tx_data, output reg tx, output reg tx_busy);
	//2^c_width > d_width+3
	reg [c_width-1:0] tx_cnt;
	reg tx_state;
	reg [d_width+1:0] tx_buffer;

	always @(posedge clk) begin
		if(rst == 1) begin
			tx_cnt = 0;
			tx = 1;
			tx_busy = 0;
			tx_state = 0;
		end
		if(tx_state == 0) begin
			if(tx_ena == 1) begin
				tx_buffer = {tx_data, 2'b01};
				tx_busy = 1;
				tx_cnt = 0;
				tx_state = 1;
			end
			else
				tx_busy = 0;
		end
		else if(tx_state == 1) begin
			if(tx_cnt < d_width+3) begin
				tx_busy = 1;
				tx_cnt = tx_cnt + 1;
				tx_buffer = {1'b1, tx_buffer[d_width+1:1]};
			end
			else begin
				tx_cnt = 0;
				tx_state = 0;
				tx_busy = 0;
			end
		end
		tx = tx_buffer[0];
	end
    p1: assert property (@(posedge clk) s_eventually !rst -> !tx_state);
    // FG !rst -> GF tx_state == 0
endmodule
