`define RESET_S	3'b000
`define FIRST_S	3'b001
`define SECOND_S	3'b010
`define THIRD_S	3'b011
`define OUTPUT_S	3'b100

module fir_fsm(clock, reset, in_valid, state_out);
input clock;
input reset;
input in_valid;

output [31:0] state_out;

reg [3:0] state;
reg [31:0] state_tmp;
reg [31:0] state_out;



always @(posedge clock)
begin
  if(reset == 1'b1)
  begin
    state <= `RESET_S;
  end
  else
  begin
    case(state)
      `RESET_S:
      begin
        state = `FIRST_S;
        state_tmp = 0;
        state_out = state_tmp;
      end
      `FIRST_S:
      begin
        if(in_valid == 1)
        begin
          state = `SECOND_S;
        end
        state_tmp = 1;
        state_out = state_tmp;
      end
      `SECOND_S:
      begin
        state = `THIRD_S;
        state_tmp = 2;
        state_out = state_tmp;
      end
      `THIRD_S:
      begin
        state = `OUTPUT_S;
        state_tmp = 3;
        state_out = state_tmp;
      end
      default:
      begin
        state = `FIRST_S;
        state_tmp = 4;
        state_out = state_tmp;
      end
    endcase
    assert property1: (state == `RESET_S || state == `FIRST_S || state == `SECOND_S || state == `THIRD_S || state == `OUTPUT_S);
  end
end
endmodule


module fir_data(reset, state_out, sample, result, output_data_ready);
input [31:0] state_out;
input reset;
input [31:0] sample;

output [31:0] result;
output output_data_ready;

wire [8:0] coefs0; 
wire [8:0] coefs1; 
wire [8:0] coefs2; 
wire [8:0] coefs3; 
wire [8:0] coefs4; 
wire [8:0] coefs5; 
wire [8:0] coefs6; 
wire [8:0] coefs7; 
wire [8:0] coefs8; 
wire [8:0] coefs9; 
wire [8:0] coefs10; 
wire [8:0] coefs11; 
wire [8:0] coefs12; 
wire [8:0] coefs13; 
wire [8:0] coefs14; 
wire [8:0] coefs15; 

reg [7:0] sample_tmp;
reg [18:0] acc; 
reg [7:0] shift0;
reg [7:0] shift1;
reg [7:0] shift2;
reg [7:0] shift3;
reg [7:0] shift4;
reg [7:0] shift5;
reg [7:0] shift6;
reg [7:0] shift7;
reg [7:0] shift8;
reg [7:0] shift9;
reg [7:0] shift10;
reg [7:0] shift11;
reg [7:0] shift12;
reg [7:0] shift13;
reg [7:0] shift14;
reg [7:0] shift15;
//reg [5:0]
integer i;
reg [31:0] result;
reg output_data_ready;
reg [31:0] state;

assign coefs0 = -6;
assign coefs1 = -4;
assign coefs2 = 13;
assign coefs3 = 16;
assign coefs4 = -18;
assign coefs5 = -41;
assign coefs6 = 23;
assign coefs7 = 154;
assign coefs8 = 222;
assign coefs9 = 154;
assign coefs10 = 23;
assign coefs11 = -41;
assign coefs12 = -18;
assign coefs13 = 16;
assign coefs14 = 13;
assign coefs15 = -4;

always @(reset or state_out or sample) 
begin
  if (reset == 1'b1)
  begin
    sample_tmp = 0;
    acc = 0;
    //for(i = 0; i <= 15; i = i+1) begin
    shift0 = 0;
    shift1 = 0;
    shift2 = 0;
    shift3 = 0;
    shift4 = 0;
    shift5 = 0;
    shift6 = 0;
    shift7 = 0;
    shift8 = 0;
    shift9 = 0;
    shift10 = 0;
    shift11 = 0;
    shift12 = 0;
    shift13 = 0;
    shift14 = 0;
    shift15 = 0;
    //end
    assert property2: state == state_out;
  end

  result = 0;
  output_data_ready = 0;
  state = state_out;

  case (state)
    1:
    begin
      sample_tmp = sample;
      acc = sample_tmp*coefs0;
      acc = acc + shift14* coefs15;
      acc = acc + shift13*coefs14;
      acc = acc + shift12*coefs13;
      acc = acc + shift11*coefs12;
    end
    2:
    begin
      acc = acc + shift10*coefs11;
      acc = acc + shift9*coefs10;
      acc = acc + shift8*coefs9;
      acc = acc + shift7*coefs8;
    end
    3:
    begin
      acc = acc + shift6*coefs7;
      acc = acc + shift5*coefs6;
      acc = acc + shift4*coefs5;
      acc = acc + shift3*coefs4;
    end
    4:
    begin
      acc = acc + shift2*coefs3;
      acc = acc + shift1*coefs2;
      acc = acc + shift0*coefs1;
      //for(i=14; i>=0; i=i-1) 
      //begin
        shift15 = shift14;
        shift14 = shift13;
        shift13 = shift12;
        shift12 = shift11;
        shift11 = shift10;
        shift10 = shift9;
        shift9 = shift8;
        shift8 = shift7;
        shift7 = shift6;
        shift6 = shift5;
        shift5 = shift4;
        shift4 = shift3;
        shift3 = shift2;
        shift2 = shift1;
        shift1 = shift0;
      //end 
      shift0 = sample;
      result = acc; 
      output_data_ready = 1;
    end
  endcase
end

endmodule


module main(SAMPLE, IN_VALID, RESET, CLK, OUTPUT_DATA_READY, RESULT);
input [31:0] SAMPLE;
input	IN_VALID;
input RESET;
input CLK;

output OUTPUT_DATA_READY;
output [31:0] RESULT;

wire [31:0] state_out;
wire [31:0] result_ins;
wire output_data_ready_ins;

reg [31:0] RESULT;
reg OUTPUT_DATA_READY;

fir_fsm fir_fsm1 (.clock(CLK), .reset(RESET), .in_valid(IN_VALID), .state_out(state_out));

fir_data fir_data1 (.reset(RESET), .state_out(state_out), .sample(SAMPLE), .result(result_ins), .output_data_ready(output_data_ready_ins));

always @(posedge CLK)
begin
  RESULT = result_ins;
  OUTPUT_DATA_READY = output_data_ready_ins;
end

endmodule

