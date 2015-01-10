`define A 2'b00
`define B 2'b01
`define C 2'b10
`define X 2'b11

`define IDLE 2'b00
`define READY 2'b01
`define BUSY 2'b10

`define NO_REQ 2'b00
`define REQ 2'b01
`define HAVE_TOKEN 2'b10

module main(clk, ackA, ackB, ackC);
input clk;
output ackA, ackB, ackC;

wire [1:0] sel;
wire active;

wire pass_tokenA, pass_tokenB, pass_tokenC;
wire reqA, reqB, reqC;

assign active = pass_tokenA || pass_tokenB || pass_tokenC;

controller controllerA(clk, reqA, ackA, sel, pass_tokenA, 2'b00);
controller controllerB(clk, reqB, ackB, sel, pass_tokenB, 2'b01);
controller controllerC(clk, reqC, ackC, sel, pass_tokenC, 2'b10);
arbiter arbiter(clk, sel, active);

client clientA(clk, reqA, ackA);
client clientB(clk, reqB, ackB);
client clientC(clk, reqC, ackC);
always assert p1: !(ackA==1 && ackB==1 || ackB==1 && ackC==1 || ackC==1 && ackA==1);
endmodule

module controller(clk, req, ack, sel, pass_token, id);
input clk, req;
input [1:0] sel;
input [1:0] id;
output ack, pass_token;

reg ack, pass_token;
reg[1:0] state;

initial state = `IDLE;
initial ack = 0;
initial pass_token = 1;

wire is_selected;
assign is_selected = (sel == id);

always @(posedge clk) begin
  if(state == 2'b00) begin
//    2'b00:
      if (is_selected) begin
        if (req) begin
          state = `READY;
          pass_token = 0; /* dropping off this line causes a safety bug */
        end
        else
          pass_token = 1;
      end
      else
        pass_token = 0;
   end
   else if(state == 2'b01) begin
//    2'b01:
//      begin
      state = `BUSY;
      ack = 1;
  end
  else if(state == 2'b10) begin
//    2'b10:
      if (!req)begin
        state = `IDLE;
        ack = 0;
        pass_token = 1;
      end
   end
//  endcase
end
endmodule

module arbiter(clk, sel, active);
input clk, active;
output [1:0] sel;

reg [1:0] state;

initial state = 2'b00;

assign sel = active ? state: 2'b11;

always @(posedge clk) begin
  if (active) begin
  if(state == 2'b00) begin
        state = 2'b01;
  end
  else if(state == 2'b01) begin
        state = 2'b10;
  end
  else if(state == 2'b10) begin
        state = 2'b00;
  end
  end
end
endmodule

module client(clk, req, ack);
input clk, ack;
output req;

reg req;
reg[1:0] state;

wire rand_choice;

initial req = 0;
initial state = `NO_REQ;


always @(posedge clk) begin
//  case(state)
    if(state == 2'b00) begin
//    2'b00:
      if (rand_choice)   begin
        req = 1;
        state = `REQ;
        end
    end
   else if(state == 2'b01) begin
//    2'b01:
      if (ack)
        state = `HAVE_TOKEN;
   end
    else if(state == 2'b10) begin
      if (rand_choice)     begin
        req = 0;
        state = `NO_REQ;
        end
   end
//  endcase
end
endmodule
