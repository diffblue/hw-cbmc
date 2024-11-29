module VGA #(localparam  size = 10, h_bits = 10, v_bits = 9)(input clk, input rst, output reg disp_ena, output reg n_blank, output reg n_sync, output reg [h_bits-1:0] col, output reg [v_bits-1:0] row);
	localparam h_pixels = 50*size;
	localparam h_pulse = 5*size;
	localparam h_bp = 8*size;
	localparam h_fp = 3*size;
	localparam h_pol = 0;

	localparam v_pixels =  25*size;
	localparam v_pulse = size;
	localparam v_bp = 1*size;
	localparam v_fp = size;
	localparam v_pol = 1;

	localparam h_period = h_pulse + h_bp + h_pixels + h_fp;
	localparam v_period = v_pulse + v_bp + v_pixels + v_fp;

	reg [h_bits-1:0] h_cnt;
	reg [v_bits-1:0] v_cnt;
	reg h_sync;
	reg v_sync;
	always @(posedge clk) begin
		if(rst == 1) begin
			h_cnt = 0;
			v_cnt = 0;
			h_sync = ~h_sync;
			v_sync = ~v_sync;
			disp_ena = 0;
			col = 0;
			row = 0;
		end
		else begin
			if(h_cnt < h_period - 1)
				h_cnt = h_cnt + 1;
			else begin
				h_cnt = 0;
				if(v_cnt < v_period - 1)
					v_cnt = v_cnt + 1;
				else
					v_cnt = 0;
			end
			if((h_cnt < (h_pixels + h_fp)) | (h_cnt >= (h_pixels + h_fp + h_pulse)))
				h_sync = ~h_sync;
			else
				h_sync = h_pol;

			if((v_cnt < (v_pixels + v_fp)) | (v_cnt >= (v_pixels + v_fp + v_pulse)))
				v_sync = ~v_sync;
			else
				v_sync = v_pol;

			if(h_cnt < h_pixels)
				col = h_cnt;

			if(v_cnt < v_pixels)
				row = v_cnt;

			if(h_cnt < h_pixels & v_cnt < v_pixels)
				disp_ena = 1;
			else
				disp_ena = 0;
		end
	end

    s2: assert property (@(posedge clk) s_nexttime (disp_ena && !rst |-> (v_sync iff s_nexttime !v_sync)));
    // X G ((disp_ena & !rst) -> ((v_sync <-> X !v_sync) | (!v_sync <-> X v_sync)))
endmodule
