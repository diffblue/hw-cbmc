module struct_packet(input clk, input [63:0] data_in, input valid,
                    output reg [63:0] data_out, output reg out_valid);

  typedef struct packed {
    logic [15:0] src_addr;
    logic [15:0] dst_addr;
    logic [7:0]  proto;
    logic [7:0]  flags;
    logic [15:0] payload;
  } packet_t;

  packet_t pkt_in, pkt_reg, pkt_out;

  always @(posedge clk) begin
    pkt_in = data_in;

    // Pipeline stage 1: register input
    pkt_reg <= pkt_in;

    // Pipeline stage 2: swap src/dst, compute checksum
    pkt_out.src_addr <= pkt_reg.dst_addr;
    pkt_out.dst_addr <= pkt_reg.src_addr;
    pkt_out.proto <= pkt_reg.proto;
    pkt_out.flags <= pkt_reg.flags | 8'h01;
    pkt_out.payload <= pkt_reg.payload ^ pkt_reg.src_addr[15:0];

    data_out <= pkt_out;
    out_valid <= valid;
  end
endmodule
