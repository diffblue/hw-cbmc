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

// *********************************************************************************************
// ebmc shows a counterexample now for p1 but the property actually holds in Jasper.
// So, this is due to the reset problem. If we force the design to be reset in 
// first cycle and then take it out of the reset for formal analysis, then we can 
// solve this problem. Or we could silently pass this giving a warning "insufficient unwinding"
// *********************************************************************************************

p1: assert property (reset_n == 1 |-> ##1 data == 0); 

endmodule
