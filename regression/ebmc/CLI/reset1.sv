module top(
  input wire                    reset_n,
  input wire                    clk,
  input wire[7:0]               A_i,
  input wire                    load_i,
  input wire                    shift_i,
  output wire                   serial_o
);
  
  wire [7:0] data_shifted;
  wire [7:0] A_plus;
  reg [7:0] data;
  assign A_plus = A_i + 8'd53;
  
  always @(posedge clk) begin
    if (reset_n) begin
          data <= 8'd00;
        end else if (load_i) begin
          data <= A_i;
        end else if (shift_i) begin
          data <= data_shifted;
        end
    end

// the below holds if the design is reset properly
p1: assert property (reset_n == 1 |-> ##1 data == 0); 

endmodule
